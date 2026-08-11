# `modelgen/interpose` — rewriting Lean's kernel from inside the process

Four files and a demo:

| file | what it is |
|---|---|
| `level_algebra.h` / `.c` | a **complete decision procedure** for Lean's universe-level algebra, over a private AST. Header carries the algorithm and its correctness argument. |
| `interpose.c` | the machine-code rewrite: find `lean::is_equivalent` and `lean::is_geq` in the host process, find their call sites, redirect them. Header carries the mechanism, the soundness story, and the environment knobs. |
| `build.sh` | `cc -shared`. No Lean headers, no Lean libraries. |
| `demo/` | the minimal standalone reproducer: one Lean file, `REJECTED` before `Lean.loadDynlib`, `ACCEPTED` after. |

Read the two `.h`/`.c` headers before anything here; they are the real
documentation. This file is the map and the warnings.

## The one-line summary

`Lean.loadDynlib` is a plain `IO` action. Native code loaded that way shares
the address space with Lean's C++ kernel. `mprotect` the kernel's `.text`,
rewrite four bytes of a `call` instruction, and `Environment.addDeclCore`
answers differently. That is the whole trick, and it needs no `sorry`, no
`native_decide`, no `@[implemented_by]`, no unsafe Lean, and no bug in Lean.

## Build and run

```bash
./build.sh                       # -> levelhack.so

# the reproducer
cd demo && lake build && ./.lake/build/bin/leveldemo ../levelhack.so

# modelgen, against a kernel that is not stock
modelgen IN.ndjson --interpose-levels /path/to/levelhack.so -o OUT.ndjson

# anything else Lean and statically linked
LD_PRELOAD=/path/to/levelhack.so some-lean-exe ...
```

## What is patched, exactly

Nine `call`/`jmp` sites, each a four-byte relative displacement, listed by the
banner at load. Five of them target `lean::is_equivalent`:

* `lean::type_checker::quick_is_def_eq` — the `Sort =?= Sort` case, which is
  the one `MODELGEN.md` §8.6 is about;
* `lean::type_checker::is_def_eq(level const&, level const&)`;
* `lean::type_checker::is_def_eq(list_ref<level> const&, ...)` — the level
  arguments of two constants;
* `lean::add_inductive_fn::check_inductive_types`;
* `lean_level_eqv` — the exported C API entry, which **nothing in the binary
  calls**, and is therefore used as a canary by the self-test.

one targets `lean::is_geq`:

* `lean::add_inductive_fn::check_constructors` — a constructor field's universe
  against the resultant universe;

and three target `lean_is_level_def_eq`, which is `Lean.Meta.isLevelDefEqAux`
compiled — the **elaborator's** level equality, an entirely different function
from the kernel's:

* `Lean.Meta.isLevelDefEq`, all three of its call sites.

Deliberately **not** patched: `lean::is_geq_core -> lean::is_geq`, the calls
into `lean::normalize`, and `Lean.Meta.solve -> lean_is_level_def_eq`. Those are
the stock algorithms' own internals, and `stock` has to keep meaning "what Lean
does", because the replacement is defined as `stock(u,v) || complete(u,v)` and
calls the untouched original.

### Why the elaborator too

Because otherwise nothing happens. `modelgen`'s level-incompleteness decline is
taken by its *planner*, which asks `Meta.isLevelDefEq` whether a candidate pad
closes the gap — the kernel never gets a chance to refuse. With the kernel alone
patched, the whole corpus comes out byte-identical. This was measured before it
was believed. `MODELGEN_LEVELHACK_META=0` reproduces that configuration.

Note that `Lean.Level.isEquiv` — the Lean-level function of that name — is a
*third* implementation again, and is not patched: nothing on the path that
matters calls it.

## Why call sites and not the function prologue

Overwriting the first bytes of `lean::is_equivalent` with a jump would destroy
the original, and recovering it needs a trampoline built by a length-aware
disassembler. Rewriting the call sites leaves the function body byte-identical
and callable at its own address, which is what lets the replacement be a strict
*extension* of the stock predicate instead of a substitute for it. It also
makes the patch selective: `is_geq_core`'s internal recursion is left alone.

## The dependency, and when this stops working

The kernel's level functions are **local** symbols (`nm` type `t`), absent from
`.dynsym`. So:

* `LD_PRELOAD` symbol interposition cannot reach them — there is no PLT
  indirection to hijack. `LD_PRELOAD` is used here only as a way to get the
  library *loaded*; the patching is done by hand.
* the host must be **unstripped**, because `.symtab` is the only place those
  addresses are written down. A stripped host makes this library abort with a
  diagnostic rather than load and do nothing.
* the host must link Lean **statically**. The shipped `libleanshared.so` is
  stripped of local symbols, so a host that uses it — including the `lean` CLI
  — cannot be patched this way. `modelgen`, `leveldemo`, and Lake executables
  generally are statically linked and unstripped, which is why this works
  there.
* the addresses are found at run time from `/proc/self/exe`; nothing is
  hardcoded, so a rebuild of the host is fine. What is hardcoded is the set of
  **mangled symbol names**, and a Lean version that renames or inlines any of
  them will make the load fail loudly.

Because the library refuses to run in a host it cannot patch, and because
`Lean.findSysroot` shells out to the (stripped) `lean` binary, the constructor
clears `LD_PRELOAD` so children do not inherit it.

## Honesty requirements this code is built around

1. **It is opt-in.** Nothing happens unless the library is loaded.
2. **It is loud.** A banner names every rewritten call site; a census at exit
   splits every level comparison into *accepted by the stock kernel*,
   *accepted only under interposition*, and *rejected by both*.
3. **A patch that does not take kills the process.** Verified by an observed
   behaviour change — the canary flips on the §8.6 witness — not by an
   `mprotect` return code. `modelgen --interpose-levels` adds two more, at the
   `addDeclCore` level and at the `Meta.isLevelDefEq` level, and refuses to run
   unless *both* flip. (Which is why the kernel-only configuration is reachable
   only through `LD_PRELOAD`: the flag promises both layers, so it checks both.)
4. **The replacement can only add acceptances**, and only ones its decision
   procedure asserts; `LA_UNKNOWN` falls back to stock. Everything the real
   kernel accepts is still accepted by the real kernel's own code.

None of that makes an interposed run a stock-kernel run. If the census reports
any escape, "checked by Lean's kernel" is false for this process, and whatever
depended on that escape has to say so.

## What this does *not* touch

this project's own `kernel/` — the Rust trusted computing base — is not involved.
The kernel being rewritten is Lean's C++ one, in the `modelgen` process, for
the duration of that process.
