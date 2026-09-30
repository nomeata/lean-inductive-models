# DAG safety: every walk over an `Expr` is linear in its DAG

**Rule: every traversal of an `Expr` in this tool is memoized, so its cost is
linear in the expression's size as a DAG — the number of distinct subterms —
and never in its size as a tree.** A recursion that descends into two children
of one node without a memo is a bug, whatever the inputs it has met so far.

## Why

An `Expr` is a DAG. A subterm that occurs twice is one object with two parents,
and `lean4export` writes it to the export's expression table once. A walk that
forgets that visits the subterm once per *path* to it, and a term of a few
hundred distinct nodes can have 2^60 paths.

That is not an exotic input. The Lean Kernel Arena's `navier-stokes-euler`
export has a structure, `EulerMeanVariationalInverse.StrongMeanEvolution`, whose
constructor type is 1,481 nodes as a DAG and 188,635,673 as a tree — typeclass
instance towers in its fields. Three unmemoized walks each expanded it:
`restore` rebuilt its recursor type into a 94-million-node term, the checker's
owner-reference certificate recorded one entry per tree occurrence of every
constant, and `findConstructorApp?` searched the tree. The run was killed at
14.5 GB; Lean's kernel checks the same export in 2.5 GB. With every walk
memoized the tool checks it, with the Arena's command line, at a peak of
2.07 GB.

A tree-size budget would be the wrong fix: it turns a walker's bug into a
decline of a legitimate declaration. The walkers are fixed instead, and the
fixtures below are a gate on them.

## How to write a walk

Use [`src/InductiveModels/ExprDag.lean`](../../src/InductiveModels/ExprDag.lean)
(`InductiveModels.Dag`), or one of Lean's walks that the table below lists as
memoized. What is available:

| need | use |
| --- | --- |
| does a subterm satisfy `p`? | `Dag.any` (Lean's `Expr.find?`) |
| the first subterm in preorder at which `f` answers | `Dag.findSome?` |
| the same question asked at every node of one walk | `Dag.anyMemo`, threading one table |
| does `e` mention a free variable? | `Dag.containsFVar`, `Dag.hasAnyFVar` (`e.containsFVarDag`, `e.hasAnyFVarDag`) |
| does `needle` occur in `e`? | `Dag.occurs` |
| a question that depends on the binder depth | `Dag.anyAt` |
| a rewrite that ignores binder depth | `Dag.map` (Lean's `Expr.replace`) |
| a rewrite that depends on binder depth | `Dag.mapAt` |
| a rewrite whose callback must recurse | `Dag.mapRec` / `Dag.mapM` |
| fold over each distinct subterm once, in preorder | `Dag.foldPreorder` |
| a count or measure computed bottom-up | `Dag.memo` over a `StateM (Dag.Memo α)` |
| DAG size; tree size, saturating | `Dag.size`; `Dag.treeSizeCapped` |

When none of these fits — a walk in `MetaM`, a walk with effects, a mutual
recursion — memoize it by hand with `Dag.memo`/`Dag.memoAt` over a
`StateT (Dag.Memo α)` or `StateT (Dag.DepthMemo α)` layered on the walk's own
monad. Examples in the tree: `Plan.spec` (depth-keyed, with the memo in the
walk's own state), `deltaDeadReduct` and
`ExactNormalizationEnv.occurrenceSurvives` (two tables: the answer per node, and
the per-node mention test every node asks of itself and its reduct),
`boxLevelOf`/`boxTyOf` (in `GenM`, under `withLocalDecl`).

Three things make a memo sound:

* **The key.** `Dag.Key` is `Lean.ExprStructEq`: pointer equality first, then
  structural equality *including* binder names and binder info, with Lean's
  cached hash. It is never `Expr` with `==`, which is alpha-equivalence and
  would hand one binder name's answer to another. A copy that lost pointer
  sharing upstream is still visited once.
* **Everything else the answer depends on is in the key or fixed for the walk.**
  A depth-dependent answer is keyed on `(node, depth)`. A walk that opens
  binders must give each opened local a fresh `FVarId`; then a term mentioning
  that local has one meaning wherever it recurs, and the node alone is a sound
  key. The exact type inference in `Check/Rules.lean` and `Format/Exact.lean`
  threads a counter for exactly this reason: it used to name locals by depth,
  which reuses a name for different binders at the same depth.
* **A rebuild returns the same object for the same input**, and an unchanged
  node as itself (`Dag.mapAt`/`Dag.mapM` rebuild with `Expr.update*!`). That is
  what keeps the *output* shared: a rebuild that allocates a fresh copy at each
  occurrence is a tree, and every later walk pays for it even if memoized.

A walk that follows only a spine — a binder telescope, an application spine,
one child per step — needs no memo. `openForalls`, `peelParams`, `headNorm`,
`instantiateForalls*` and the `whnf` loops are of that kind. So are the two
readings of an owner's type as the kernel reads it, `kernelFormer` (generator)
and `ExactNormalizationEnv.kernelFormer?` (checker): each step is one `whnf`
and one memoized `instantiate1`/`abstract` (or `mkForallFVars`) of what is
left, so the cost is the binder count times one linear pass, and a type already
written as `∀ p⃗ i⃗, Sort u` — every type Lean's elaborator writes without a
definition in the way — returns after reading its spine alone.

## Lean's own walks

What is and is not memoized in Lean v4.35.0-rc3 (the pinned toolchain), read
off its source rather than assumed. Between v4.33.0 and v4.35.0-rc3 none of
these walks changed except the two noted in the table (`foldConsts` and
`instantiateMVars`); the kernel's definitional-equality cache, below the
tables, changed too.

| memoized — linear in the DAG | how |
| --- | --- |
| `Expr.replace`, `instantiateLevelParams` | C++ `replace_fn`, a cache keyed on the pointer of every shared node |
| `instantiate`, `instantiate1`, `instantiateRev`, `instantiateRange`, `instantiateRevRange`, `abstract`, `abstractRange`, `lowerLooseBVars`, `liftLooseBVars` | C++ `replace_rec_fn`, keyed on `(pointer, binder offset)` |
| `Expr.find?`, `Expr.findExt?` | C++ `for_each` with a visited set (`findExt?` does not cache partial applications, which only ever costs a spine) |
| `Expr.hasLooseBVar` | C++ `for_each` with offsets, keyed on `(pointer, offset)` |
| `==` (`Expr.eqv`), `Expr.equal` | C++ `expr_eq_fn`, with a cache of shared pointer *pairs* |
| `foldConsts`, `getUsedConstants` | a `PtrSet` of visited nodes; since leanprover/lean4#14728 (v4.34.0) they also count a projection's structure name. `Order.lean` keeps its own copy of this walk because one visited set spans all of a record's roots |
| `collectFVars`, `collectLevelParams`, `forEach` | an `ExprSet` or `MonadCacheT` of visited nodes |
| `Meta.transform`, `Core.transform`, `instantiateMVars` | a cache keyed on `ExprStructEq`; `instantiateMVars` also caches its lifts of substituted values, keyed on `(pointer, cutoff, amount)`, since leanprover/lean4#14520 (v4.34.0) |
| `hash`, `hasLooseBVars`, `looseBVarRange`, `hasFVar`, `approxDepth` | stored in every node: constant time |

| **not** memoized | instead |
| --- | --- |
| `Expr.containsFVar`, `Expr.hasAnyFVar` | `Dag.containsFVar`, `Dag.hasAnyFVar` — the core ones stop only where `hasFVar` is false |
| `Expr.replaceNoCache`, `instantiateLevelParamsNoCache` | the cached forms |
| `Expr.sizeWithoutSharing` | `Dag.size`, `Dag.treeSizeCapped` |
| `toString`/`dbgToString` of an `Expr`, and `MessageData.ofExpr` rendered *without* a context | never print an `Expr` that way; with an environment in context the delaborator stops at `pp.maxSteps` (5000) and elides deep terms (`pp.deepTerms` is off), which is how kernel exceptions are rendered here |
| `Expr.quickLt`, `Expr.lt` | plain recursion, but into one child per step after a cached equality test: polynomial, never exponential; not used on a hot path |

`test/scripts/check-dag-safe-calls.sh` fails the build matrix if a source file
calls one of the unmemoized ones.

**Structural caches degrade on copies.** Lean's kernel and `Meta.inferType`
cache on structural keys, and an equality test between two structurally equal
terms that are *different objects* costs their size, with a fresh pair cache
each time. That includes the kernel's definitional-equality caches: since
leanprover/lean4#14806 (v4.34.0) a successful `is_def_eq` is recorded in a plain
set of expression pairs, like a failed one, where it used to be merged into a
union-find (`equiv_manager`) that walked both terms under a pointer-keyed node
map. Both sets hash and compare their keys structurally. Instantiating the parameters of an open tower — a `Π` tower over a
parameter, say — produces such copies, one per binder offset the tower appears
at, and both then run quadratic in the tower rather than linear. That is Lean's
behavior on its own terms, polynomial, and visible only on adversarial arrow
towers: a structure with one field of type `α → α → …` nested to depth 30, 60
and 120 over `α : Sort u` costs 1.0, 7.3 and 96 billion instructions to model,
almost all of it in `Meta.inferType` and the kernel's caches. It is recorded
here so that nobody mistakes it for one of ours.

## The coercions the recursive box builds

`boxValOf`/`unboxValOf` (`src/InductiveModels/Simple/Box.lean`) are not walks:
they *construct* a coercion between a field type and its recursively boxed
form, and at `Π d, b` the coercion mentions a coercion at `d` and one at `b`.
Written as λ-terms, with the sub-coercions inlined under a fresh variable each,
the coercion for a `Π` tower whose domain and codomain share structure was as
large as that structure's *tree*: a field of type `(α → γ) → (α → γ)` nested,
with `α : Sort u`, `γ : Sort v`, cost 1.1·10^10 instructions at depth 12 and
did not finish at depth 20. The box now writes every coercion as an
application of a generic combinator (`arrBox uD bC`, `arrUnbox bD uC`, and
dependent forms) to its children's coercions, memoized on the type, so the
coercion terms are a DAG as large as the field type's.

**That is not enough on its own, because the kernel converts the round trip.**
Every ι rule of a boxed model rests on `unbox (box v) ≡ v`, and the recursor on
`box (unbox p) ≡ p`. Both hold by βδι and function eta, and Lean's kernel
decides them by eta-expanding the value at every `Π` and comparing the
argument's own round trip at a *fresh* variable, and so on down: one question
per node of the tree. Its caches cannot share those questions — each is about
a different free variable, so no two are the same pair. Stating the round
trip over closed per-node functions, `(fun x => unbox (box x)) = (fun x => x)`,
does not help either: the kernel opens both sides with one fresh variable and
the recurring pairs below are again open. Measured against Lean's kernel on
v4.35.0-rc3 (the plain pair cache that replaced the union-find one,
leanprover/lean4#14806), with the coercions as shared constants, the
`Eq.refl` check of the round trip costs 6.3·10^7, 1.9·10^8, 6.8·10^8 and
2.6·10^9 instructions at depths 8, 10, 12 and 14, in the pointwise and the
closed form alike: a factor of four every two levels. v4.33.0 measured the
same.

So the round trips are **lemmas**: every node has `rt : ∀ v, unbox (box v) = v`
and `sec : ∀ w, box (unbox w) = w`, again applications of four generic lemmas
(`arrRt`, `arrSec`, `depRt`, `depSec`) to the children's, each proved once
about variables from one `Eq.rec` and one `funext`. Where no later field names
a boxed field, the tuple tower's destructor applies the minor at the unboxed
value and transports the result along `sec` through one generic `boxFix`; its
ι rule is proved by one generic `boxFix_iota` per such field, which takes the
field's `rt`; its selectors and the empty arm's return `unbox (box f)`, whose
projection rule is `rt f`. The transports are definitions at reducibility
height `0` — the kernel unfolds them last, so the `Eq.rec` inside, whose K-like
reduction would ask the very round trip, is reached only where the other side
is stuck — and at a *regular* height rather than an opaque one, because the
kernel compares two applications of the same definition argument by argument
before unfolding them only for regular definitions. The cost is `funext`, and
with it `Quot.sound`, in every such model's ι proofs.

A boxed field that a later field's type names is still converted: that type is
stated at the unboxed value, the tuple holding it at the stored one, and the
projection rule's statement needs the conversion to be well typed at all.

The whole model of the depth-`k` tower now costs, instructions for the run
with every check on, on v4.35.0-rc3:

| depth | `main` | now |
| ---: | ---: | ---: |
| 8 | 9.5·10^8 | 4.9·10^8 |
| 12 | 1.1·10^10 | 5.8·10^8 |
| 14 | 4.6·10^10 | 6.5·10^8 |
| 30 | — | 2.1·10^9 |
| 60 | — | 1.7·10^10 |
| 120 | — | 2.1·10^11 |

The growth past depth 30 is the open-tower cost described above (structural
caches degrading on copies), not the box's: an unboxed field of the same shape,
`α → α → …` over `α : Sort u`, costs 1.9·10^10 and 2.8·10^11 at depths 60 and
120.

**The tree arm boxes the same way, in two towers.** A branching owner stores
its fields in a data tower and a recursive field's binders in a branch tower,
and a boxed component either of them holds is a slot under the same rule: boxed,
and named by nothing after it — for a stored field, neither a later stored
field nor a recursive field's binder. The recursor's minor for a constructor
goes through `boxFix` at each data slot, with the children and their
hypotheses in the motive (untagged, their type names the label that holds the
slot); the eta lemma `dispatch = f` goes through `boxFix` at each branch slot
and the slot's `rt`; and the eta transport is the box's `cast` wherever a
branch slot makes the lemma's endpoints differ by a round trip. The ι rule of a
constructor with a slot is then `WT.Wrec_iota`, one `boxFix_iota` per data
slot, and an `Eq.rec` per child with a branch slot along
`(fun z⃗ => k (unbox (box z⃗))) = k` — `funext` over the slot's `rt` — after
which the eta transport's endpoints are one term and its K-like reduction
closes the rule. A one-constructor owner's selector returns `unbox (box f)`, and
its rule is `rt f`. A branching owner with a boxed arrow-tower leaf cost
3.2·10^9 and 8.9·10^9 instructions at depths 12 and 14 before; the three
owners of `box_tree_tower` (depth 30) now cost 7.2·10^9 together.

**The mutual one-layer adapter does not box.** Its laws and ι rules are
reflexivity and stand only where `unroll (roll v) ≡ v` is a cheap conversion,
which a boxed field's is not; it never stored one either — its public
constructor stored the field unboxed and was refused by name, an internal
error at every depth. A member that would store a boxed field therefore keeps
its private carrier, like a multi-constructor member, and the block's private
family models it through the tuple tower or the tree arm, which box with the
lemmas above (`box_mutual_tower`, depth 30: 3.8·10^9 instructions).

## The fixtures that gate it

[`test/fixtures/dag-towers/`](../../test/fixtures/dag-towers/) puts a depth-60
tower — about 2^60 nodes as a tree, a few hundred as a DAG; depth 30 in the two
newest box fixtures — into every record
position the tool reads: constructor field types (closed, open over a
parameter, open over an earlier field, in `Prop`, in an index, as the domain of
a function field), projection bodies, recursive and mutual and nested blocks,
theorem types and values, axiom and quotient types, `Prod` towers of the
instance-tower kind, and arrow towers that no reduction shrinks. Most are
con-leche's, ported as complete kernel exports; `ctor_field_towers` and the
three `box_*` fixtures are this repository's own — the latter the recursive
box's construction gates rather than walk gates, one per route that stores a
boxed field (`box_tower` the tuple tower, `box_tree_tower` the tree arm,
`box_mutual_tower` a mutual block the one-layer adapter used to claim).
`test/scripts/check_fixture_verdicts.py` runs each one and
fails it if it is not accepted, if its peak resident set exceeds 1 GiB, or if
it needs more than 120 s of CPU.

The bound is what makes the gate deterministic. A linear walk keeps every tower
fixture near 100 MiB and well under a second; a walk that expands any tower once
cannot stay under 1 GiB — or, if it expands without allocating, cannot finish in
any time — whatever machine it runs on. The CPU bound only decides how long
that takes to observe. On the `main` of 2026-09-29 eight of the fifteen tower
fixtures fail it: six are killed at 1 GiB, and two exhaust the CPU bound. On
`435f7c1` `box_tower` is killed at 1 GiB, and on `e9b69bf` so are
`box_tree_tower` and `box_mutual_tower`.

A new walk is not covered because a fixture happens to pass: the rule above is
the contract, and the fixtures only catch the walks their records reach. When a
new record position or route is added, add a tower to it.
