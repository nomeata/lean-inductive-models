/*
  interpose.c — rewrite Lean's kernel, in memory, at run time.

  # What this does, in one sentence

  When this shared object is loaded into an unstripped, statically-Lean-linked
  Lean executable, its ELF constructor finds the machine code of Lean's level
  comparison functions in the host process, finds selected *call sites* of
  those functions, and rewrites the four-byte relative displacement of each
  call so that Lean calls this library instead.

  Three functions are targeted, in two different layers of Lean:

    * `lean::is_equivalent` and `lean::is_geq` — the C++ **kernel**, reached
      from `Environment.addDeclCore`;
    * `lean_is_level_def_eq` (`Lean.Meta.isLevelDefEq`) — the **elaborator**,
      which is compiled Lean and a *completely different function*.

  Both layers are needed, and finding that out is the main measurement result
  here.  `modelgen`'s §8.6 decline is taken by its planner, which asks
  `Meta.isLevelDefEq` whether a candidate pad closes a level gap.  With only
  the kernel patched, the planner still refuses and the corpus does not move at
  all — measured, ~190 files, every report identical.  With both patched, the
  `BoxF` carrier is planned *and* accepted.

  # Why this exists

  Two reasons, both stated in the task that produced it.

  1. `modelgen` declines one shape (`MODELGEN.md` §8.6, the `BoxF` carrier)
     purely because Lean's universe-level definitional equality is incomplete:
     a `max` does not absorb an `imax` it dominates.  With a complete level
     procedure in place the kernel accepts the model, so `modelgen` can be
     measured against Lean's *actual* kernel rather than against a
     reimplementation of it.

  2. It is a demonstration.  This repository carries a standing warning that
     meta-level code can subvert the kernel.  This is that warning, executable:
     a `Lean.loadDynlib` from ordinary Lean `IO` changes what `addDeclCore`
     accepts.  Nothing here needs `sorry`, `native_decide`, or an `@[implemented_by]`.

  # What it does NOT do

  It does not touch this project's own `kernel/`.  That is a separate, Rust,
  trusted computing base and it is untouched by any of this.  The thing being
  subverted here is *Lean's* C++ kernel, inside the `modelgen` process.

  # The extension is one-sided, and that is the whole soundness story

  The replacement never *removes* an acceptance and never *invents* one on its
  own authority:

      hook(u, v)  =  stock(u, v)  ||  complete(u, v)

  `stock` is the untouched original function, still present at its original
  address (only call sites were rewritten, not the function body), so
  everything the real kernel accepts is still accepted for the same reason.
  The only new acceptances come from `complete`, the decision procedure in
  `level_algebra.c`, and only when it returns LA_TRUE — LA_UNKNOWN falls back.

  Every such new acceptance is *counted*.  That counter is the population
  "accepted only under interposition", and it is reported on stderr at exit.
  A run with `escapes = 0` was, for level comparisons, a stock kernel run.

  # Dependency: the host binary must be unstripped

  `lean::is_equivalent` and `lean::is_geq` are *local* symbols (`nm` type `t`).
  They are absent from the dynamic symbol table, so `LD_PRELOAD` symbol
  interposition cannot reach them; there is no PLT indirection to hijack.  This
  library therefore reads the host's *full* symbol table (`.symtab`) out of
  `/proc/self/exe`.

  A stripped host has no `.symtab`, and then this library **aborts the process
  with a diagnostic** rather than loading and doing nothing.  A host with no
  Lean runtime in it at all — `timeout`, `env`, `sh`, whatever else an
  `LD_PRELOAD` line drags in — is a different case and is left alone with a
  note: it was never the host anyone meant to patch.  The same is true
  of a host that links `libleanshared.so` instead of static Lean: the shipped
  `libleanshared.so` is stripped of local symbols, so the kernel's level
  functions are not findable there either.  `modelgen` is statically linked and
  unstripped, which is why this works on `modelgen`.

  # How to use it

    * `LD_PRELOAD=.../levelhack.so <lean-exe> ...`   — patch, no host support
      needed; or
    * `Lean.loadDynlib "…/levelhack.so"` from inside the host — same effect,
      opt-in from Lean code.  `modelgen --interpose-levels` does this.

  Environment:

    * `MODELGEN_LEVELHACK=off`     — load but patch nothing (A/B control).
    * `MODELGEN_LEVELHACK_META=0`  — patch the kernel only, leaving the
      elaborator stock.  The configuration that demonstrably moves nothing.
    * `MODELGEN_LEVELHACK_TRACE=1` — print every escaping pair on stderr.
    * `MODELGEN_LEVELHACK_FUZZ=N`  — on the first level comparison, run an
      N-pair fuzz of stock vs. complete vs. a bounded semantic oracle, print
      the table, and exit.  A measurement mode; it terminates the process.

  # Verification that the patch took

  Two independent checks, neither of which is "mprotect returned 0":

    * *bytes*: after patching, every rewritten displacement is read back and
      must point at the trampoline.
    * *behaviour*: the first time a hook runs, a self-test calls the exported
      `lean_level_eqv` — which is one of the patched call sites and has no
      other caller in the binary, so it serves as a canary — on the §8.6
      witness pair.  Stock says "not equivalent"; the patched path must say
      "equivalent".  If it does not, the process dies with exit 70.

  The `modelgen` side adds a third and a fourth: it replays the §8.6
  declaration through `addDeclCore`, and asks `Meta.isLevelDefEq` the §8.6
  question, and requires *both* verdicts to flip.
*/

#define _GNU_SOURCE
#include <dlfcn.h>
#include <elf.h>
#include <fcntl.h>
#include <link.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <errno.h>
#include <unistd.h>

#include "level_algebra.h"

/* ================================================================== */
/* Lean object access.                                                */
/*                                                                    */
/* Deliberately not `#include <lean/lean.h>`: the only thing needed on */
/* the hot path is the constructor tag and the object fields, and      */
/* open-coding them keeps this library free of link-time dependencies  */
/* on the host's Lean runtime.  Layout verified against v4.29.1:       */
/* `lean_object` is { int m_rc; uint16 m_cs_sz; uint8 m_other;         */
/* uint8 m_tag; }, i.e. the tag is byte 7, and constructor fields      */
/* start at byte 8.  `Lean.Level` is                                   */
/*   0 zero (scalar)  1 succ u  2 max u v  3 imax u v                  */
/*   4 param n        5 mvar id                                        */
/* each with a trailing `@[computed_field] data : UInt64`, which sits   */
/* after the object fields and is never read here.                     */
/* ================================================================== */

#define LO_IS_SCALAR(o) (((uintptr_t)(o) & 1) != 0)
#define LO_UNBOX(o)     ((uintptr_t)(o) >> 1)

static inline unsigned lo_tag(void *o) {
  return LO_IS_SCALAR(o) ? (unsigned)LO_UNBOX(o)
                         : (unsigned)((unsigned char *)o)[7];
}
static inline void *lo_field(void *o, unsigned i) {
  return ((void **)((char *)o + 8))[i];
}

enum { LVL_ZERO = 0, LVL_SUCC = 1, LVL_MAX = 2, LVL_IMAX = 3,
       LVL_PARAM = 4, LVL_MVAR = 5 };

/* ================================================================== */
/* Diagnostics.                                                       */
/* ================================================================== */

static void lh_say(const char *fmt, ...) {
  char buf[2048];
  va_list ap;
  va_start(ap, fmt);
  int n = vsnprintf(buf, sizeof(buf), fmt, ap);
  va_end(ap);
  if (n > 0) {
    ssize_t ignored = write(2, buf, (size_t)n < sizeof(buf) ? (size_t)n
                                                            : sizeof(buf) - 1);
    (void)ignored;
  }
}

static void lh_die(const char *fmt, ...) {
  char buf[2048];
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(buf, sizeof(buf), fmt, ap);
  va_end(ap);
  lh_say("[levelhack] FATAL: %s\n", buf);
  lh_say("[levelhack] refusing to continue: an interposition that silently "
         "does nothing is worse than no interposition.\n");
  _exit(70);
}

/* ================================================================== */
/* Host ELF symbol table.                                             */
/* ================================================================== */

typedef struct {
  uintptr_t   addr; /* link-time address */
  uintptr_t   size;
  const char *name;
} lh_sym;

static struct {
  uintptr_t base;      /* PIE load bias */
  char     *image;     /* mmap of /proc/self/exe */
  size_t    image_len;
  lh_sym   *syms;      /* sorted by addr */
  size_t    nsyms;
  uintptr_t text_addr; /* link-time */
  uintptr_t text_size;
} H;

static int lh_phdr_cb(struct dl_phdr_info *info, size_t sz, void *data) {
  (void)sz;
  if (info->dlpi_name && info->dlpi_name[0] != '\0') return 0;
  *(uintptr_t *)data = (uintptr_t)info->dlpi_addr;
  return 1;
}

static void lh_load_symbols(void) {
  uintptr_t base = (uintptr_t)-1;
  dl_iterate_phdr(lh_phdr_cb, &base);
  if (base == (uintptr_t)-1)
    lh_die("could not find the main executable's load bias via dl_iterate_phdr");
  H.base = base;

  int fd = open("/proc/self/exe", O_RDONLY);
  if (fd < 0) lh_die("cannot open /proc/self/exe");
  struct stat st;
  if (fstat(fd, &st) != 0) lh_die("cannot stat /proc/self/exe");
  char *img = mmap(NULL, (size_t)st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  close(fd);
  if (img == MAP_FAILED) lh_die("cannot mmap /proc/self/exe");
  H.image = img;
  H.image_len = (size_t)st.st_size;

  Elf64_Ehdr *eh = (Elf64_Ehdr *)img;
  if (memcmp(eh->e_ident, ELFMAG, SELFMAG) != 0)
    lh_die("/proc/self/exe is not an ELF file");
  Elf64_Shdr *sh = (Elf64_Shdr *)(img + eh->e_shoff);
  const char *shstr = img + sh[eh->e_shstrndx].sh_offset;

  Elf64_Shdr *symtab = NULL, *strtab = NULL;
  for (int i = 0; i < eh->e_shnum; i++) {
    const char *nm = shstr + sh[i].sh_name;
    if (sh[i].sh_type == SHT_SYMTAB) {
      symtab = &sh[i];
      strtab = &sh[sh[i].sh_link];
    }
    if (strcmp(nm, ".text") == 0) {
      H.text_addr = sh[i].sh_addr;
      H.text_size = sh[i].sh_size;
    }
  }
  if (!symtab)
    lh_die("the host executable has no .symtab — it is stripped.\n"
           "        lean::is_equivalent and lean::is_geq are LOCAL symbols; "
           "they are not in .dynsym,\n"
           "        so there is nothing left to find.  Build the host "
           "unstripped (Lake's default) or\n"
           "        bake the offsets in at build time.");
  if (!H.text_size) lh_die("the host executable has no .text section header");

  size_t n = symtab->sh_size / sizeof(Elf64_Sym);
  Elf64_Sym *sy = (Elf64_Sym *)(img + symtab->sh_offset);
  const char *str = img + strtab->sh_offset;
  H.syms = calloc(n, sizeof(lh_sym));
  if (!H.syms) lh_die("out of memory building the symbol index");
  size_t k = 0;
  for (size_t i = 0; i < n; i++) {
    unsigned type = ELF64_ST_TYPE(sy[i].st_info);
    if (type != STT_FUNC || sy[i].st_value == 0) continue;
    H.syms[k].addr = sy[i].st_value;
    H.syms[k].size = sy[i].st_size;
    H.syms[k].name = str + sy[i].st_name;
    k++;
  }
  H.nsyms = k;
  /* Not sorted: every lookup here is by name, there are about ten of them, and
     sorting ~180k entries was measurable at load. */
}

static const lh_sym *lh_find(const char *name) {
  for (size_t i = 0; i < H.nsyms; i++)
    if (strcmp(H.syms[i].name, name) == 0) return &H.syms[i];
  return NULL;
}

/* Resolve a host function.  The symbol table read out of /proc/self/exe is
   tried first and `dlsym` only as a fallback, because a Lake executable built
   without `supportInterpreter` is not linked `-rdynamic` and exports almost
   nothing — but it still carries a full `.symtab`, which is the same thing
   this library already depends on to find `lean::is_equivalent` at all. */
static void *lh_host(const char *name) {
  const lh_sym *s = lh_find(name);
  if (s) return (void *)(H.base + s->addr);
  return dlsym(RTLD_DEFAULT, name);
}

/* ================================================================== */
/* Patch plan.                                                        */
/* ================================================================== */

typedef struct {
  const char *owner;  /* mangled symbol of the calling function */
  const char *label;  /* what to print */
  int         found;
} lh_allow;

static lh_allow allow_equiv[] = {
  {"_ZN4lean12type_checker15quick_is_def_eqERKNS_4exprES3_b",
   "type_checker::quick_is_def_eq   (Sort =?= Sort)", 0},
  {"_ZN4lean12type_checker9is_def_eqERKNS_5levelES3_",
   "type_checker::is_def_eq(level)", 0},
  {"_ZN4lean12type_checker9is_def_eqERKNS_8list_refINS_5levelEEES5_",
   "type_checker::is_def_eq(levels) (const level args)", 0},
  {"_ZN4lean16add_inductive_fn21check_inductive_typesEv",
   "add_inductive_fn::check_inductive_types", 0},
  {"lean_level_eqv",
   "lean_level_eqv                  (canary; no other caller)", 0},
};

static lh_allow allow_geq[] = {
  {"_ZN4lean16add_inductive_fn18check_constructorsEv",
   "add_inductive_fn::check_constructors", 0},
};

/* The *elaborator's* level equality, which is a different function from the
   kernel's and is where `modelgen`'s planner actually asks its question.
   `Lean.Meta.isLevelDefEq` is compiled to `lean_is_level_def_eq` (six
   pointer arguments, all in registers, no stack arguments); the single site
   below is `Lean.Meta.isLevelDefEq` itself.

   Deliberately NOT patched: `Lean.Meta.solve` -> `lean_is_level_def_eq`, which
   is the level-defeq algorithm's own internal recursion, and
   `Lean.Meta.isDefEqQuick`, which is expression defeq and not what the planner
   calls. */
static lh_allow allow_meta[] = {
  {"l_Lean_Meta_checkpointDefEq___at___00Lean_Meta_isLevelDefEq_spec__0",
   "Lean.Meta.isLevelDefEq          (the elaborator, not the kernel)", 0},
};

/* Deliberately NOT patched: lean::is_geq_core -> lean::is_geq and
   lean::is_geq_core -> lean::normalize, which are the stock algorithm's own
   internal recursion.  Rewriting those would change what `stock` means, and
   `stock` has to keep meaning "what Lean's kernel does". */

/* ================================================================== */
/* Counters.                                                          */
/* ================================================================== */

static struct {
  unsigned long equiv_calls, equiv_stock_true, equiv_escape, equiv_both_false,
      equiv_unknown;
  unsigned long geq_calls, geq_stock_true, geq_escape, geq_both_false,
      geq_unknown;
  unsigned long meta_calls, meta_stock_true, meta_escape, meta_both_false,
      meta_unflippable;
} C;

static int lh_trace = 0;
static int lh_active = 0;
/* Patch the elaborator's Lean.Meta.isLevelDefEq as well as the kernel.  On by
   default: `modelgen`'s planner asks its level questions there, and a
   kernel-only interposition changes nothing it decides.  Set
   MODELGEN_LEVELHACK_META=0 for the kernel-only experiment. */
static int lh_meta = 1;

#define BUMP(x) __atomic_fetch_add(&(x), 1UL, __ATOMIC_RELAXED)

/* ================================================================== */
/* Decoding a Lean level into the private AST.                        */
/* ================================================================== */

typedef struct {
  la_arena ar;
  void    *vars[LA_MAX_VARS];
  int      nvars;
  int      bail; /* mvar seen, or too many variables */
} lh_ctx;

static uint8_t (*lean_name_eq_p)(void *, void *);

static int lh_intern(lh_ctx *c, void *name) {
  for (int i = 0; i < c->nvars; i++) {
    if (c->vars[i] == name) return i;
    if (lean_name_eq_p && lean_name_eq_p(c->vars[i], name)) return i;
  }
  if (c->nvars >= LA_MAX_VARS) {
    c->bail = 1;
    return -1;
  }
  c->vars[c->nvars] = name;
  return c->nvars++;
}

static int32_t lh_decode(lh_ctx *c, void *l) {
  if (c->bail) return -1;
  switch (lo_tag(l)) {
    case LVL_ZERO:
      return la_mk_zero(&c->ar);
    case LVL_SUCC:
      return la_mk_succ(&c->ar, lh_decode(c, lo_field(l, 0)));
    case LVL_MAX:
      return la_mk_max(&c->ar, lh_decode(c, lo_field(l, 0)),
                       lh_decode(c, lo_field(l, 1)));
    case LVL_IMAX:
      return la_mk_imax(&c->ar, lh_decode(c, lo_field(l, 0)),
                        lh_decode(c, lo_field(l, 1)));
    case LVL_PARAM: {
      int v = lh_intern(c, lo_field(l, 0));
      if (v < 0) return -1;
      return la_mk_var(&c->ar, v);
    }
    default:
      /* metavariables: no opinion.  The kernel should never see one, and
         guessing about one is exactly the kind of thing that turns a
         soundness story into a story. */
      c->bail = 1;
      return -1;
  }
}

/* Per-thread arena, allocated on first use. */
static __thread la_node *lh_arena_storage = NULL;

static int lh_ctx_init(lh_ctx *c) {
  if (!lh_arena_storage) {
    lh_arena_storage = malloc(sizeof(la_node) * LA_ARENA_CAP);
    if (!lh_arena_storage) return 0;
  }
  la_arena_init(&c->ar, lh_arena_storage, LA_ARENA_CAP);
  c->nvars = 0;
  c->bail = 0;
  return 1;
}

/* ================================================================== */
/* The self-test and the fuzz (defined below the hooks).              */
/* ================================================================== */

static void lh_first_call_checks(void);

/* ================================================================== */
/* The hooks.                                                         */
/* ================================================================== */

static uint8_t (*orig_is_equivalent)(void **, void **);
static uint8_t (*orig_is_geq)(void **, void **);

static la_result lh_decide(void *u, void *v, int geq, char *tu, char *tv,
                           size_t tn) {
  lh_ctx c;
  if (!lh_ctx_init(&c)) return LA_UNKNOWN;
  int32_t a = lh_decode(&c, u);
  int32_t b = lh_decode(&c, v);
  if (c.bail || a < 0 || b < 0) return LA_UNKNOWN;
  if (tu) {
    la_print(&c.ar, a, tu, (int32_t)tn, NULL);
    la_print(&c.ar, b, tv, (int32_t)tn, NULL);
  }
  return geq ? la_geq(&c.ar, a, b) : la_equiv(&c.ar, a, b);
}

/* The self-test drives the canary call site on purpose; its comparison is not
   part of the host's own workload and must not enter the census. */
static int lh_in_selftest(void);

static uint8_t hook_is_equivalent(void **pu, void **pv) {
  lh_first_call_checks();
  int census = !lh_in_selftest();
  if (census) BUMP(C.equiv_calls);
  if (orig_is_equivalent(pu, pv)) {
    if (census) BUMP(C.equiv_stock_true);
    return 1;
  }
  char tu[512], tv[512];
  la_result r = lh_decide(*pu, *pv, 0, lh_trace ? tu : NULL,
                          lh_trace ? tv : NULL, sizeof(tu));
  if (r == LA_TRUE) {
    if (census) {
      BUMP(C.equiv_escape);
      if (lh_trace) lh_say("[levelhack] escape (equiv): %s  ~  %s\n", tu, tv);
    }
    return 1;
  }
  if (census) {
    if (r == LA_UNKNOWN) BUMP(C.equiv_unknown);
    BUMP(C.equiv_both_false);
  }
  return 0;
}

static uint8_t hook_is_geq(void **pu, void **pv) {
  lh_first_call_checks();
  int census = !lh_in_selftest();
  if (census) BUMP(C.geq_calls);
  if (orig_is_geq(pu, pv)) {
    if (census) BUMP(C.geq_stock_true);
    return 1;
  }
  char tu[512], tv[512];
  la_result r = lh_decide(*pu, *pv, 1, lh_trace ? tu : NULL,
                          lh_trace ? tv : NULL, sizeof(tu));
  if (r == LA_TRUE) {
    if (census) {
      BUMP(C.geq_escape);
      if (lh_trace) lh_say("[levelhack] escape (geq):   %s  >=  %s\n", tu, tv);
    }
    return 1;
  }
  if (census) {
    if (r == LA_UNKNOWN) BUMP(C.geq_unknown);
    BUMP(C.geq_both_false);
  }
  return 0;
}

/* ------------------------------------------------------------------ */
/* The elaborator hook.                                                */
/*                                                                     */
/* `lean_is_level_def_eq` is `Lean.Meta.isLevelDefEqAux` compiled: six  */
/* pointer arguments in registers, returning an `EStateM.Result`, which */
/* is a constructor with tag 0 (`ok`, fields value and state) or tag 1  */
/* (`error`).  The two `Level`s are arguments one and two and are       */
/* *owned* by the callee, so they are retained across the call.         */
/*                                                                     */
/* The flip mutates field 0 of the returned `ok` from `false` to        */
/* `true`.  `Bool` is a scalar, so no reference counting is involved,   */
/* and the result was just allocated by the callee — but if it somehow  */
/* is not uniquely referenced the flip is skipped and counted rather    */
/* than performed on an object someone else can see.                    */
/* ------------------------------------------------------------------ */

typedef void *(*lh_meta_fn)(void *, void *, void *, void *, void *, void *);
static lh_meta_fn orig_meta_ldeq;

static void lo_inc(void *o);
static void lo_dec(void *o);

#define LO_FALSE ((void *)1) /* lean_box(0) */
#define LO_TRUE  ((void *)3) /* lean_box(1) */

static void *hook_meta_ldeq(void *u, void *v, void *a3, void *a4, void *a5,
                            void *a6) {
  lh_first_call_checks();
  lo_inc(u);
  lo_inc(v);
  void *r = orig_meta_ldeq(u, v, a3, a4, a5, a6);
  BUMP(C.meta_calls);
  if (!LO_IS_SCALAR(r) && lo_tag(r) == 0 && lo_field(r, 0) == LO_FALSE) {
    char tu[512], tv[512];
    la_result q = lh_decide(u, v, 0, lh_trace ? tu : NULL,
                            lh_trace ? tv : NULL, sizeof(tu));
    if (q == LA_TRUE) {
      if (*(int *)r == 1) {
        ((void **)((char *)r + 8))[0] = LO_TRUE;
        BUMP(C.meta_escape);
        if (lh_trace)
          lh_say("[levelhack] escape (meta):  %s  ~  %s\n", tu, tv);
      } else {
        BUMP(C.meta_unflippable);
      }
    } else {
      BUMP(C.meta_both_false);
    }
  } else {
    BUMP(C.meta_stock_true);
  }
  lo_dec(u);
  lo_dec(v);
  return r;
}

/* ================================================================== */
/* Trampolines and the call-site rewrite.                             */
/* ================================================================== */

static unsigned char *lh_tramp_page = NULL;
static size_t         lh_tramp_used = 0;

static void lh_tramp_alloc_page(uintptr_t near) {
  /* Somewhere within +-2GB of .text, so a rel32 can reach it. */
  for (uintptr_t off = 0x1000000; off < 0x40000000UL; off += 0x1000000) {
    void *hint = (void *)((near + off) & ~(uintptr_t)0xFFF);
    void *p = mmap(hint, 4096, PROT_READ | PROT_WRITE | PROT_EXEC,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (p != MAP_FAILED && p == hint) {
      lh_tramp_page = p;
      return;
    }
    if (p != MAP_FAILED) munmap(p, 4096);
  }
  lh_die("could not place a trampoline page within reach of .text");
}

static unsigned char *lh_tramp(void *target) {
  unsigned char *t = lh_tramp_page + lh_tramp_used;
  lh_tramp_used += 16;
  if (lh_tramp_used > 4096) lh_die("trampoline page full");
  /* movabs $target, %r11 ; jmp *%r11   -- r11 is scratch in the SysV ABI, so
     it is safe to clobber at a call boundary. */
  t[0] = 0x49; t[1] = 0xBB;
  memcpy(t + 2, &target, 8);
  t[10] = 0x41; t[11] = 0xFF; t[12] = 0xE3;
  return t;
}

static void lh_mprotect_text(int writable) {
  uintptr_t lo = (H.base + H.text_addr) & ~(uintptr_t)0xFFF;
  uintptr_t hi = (H.base + H.text_addr + H.text_size + 0xFFF) & ~(uintptr_t)0xFFF;
  int prot = PROT_READ | PROT_EXEC | (writable ? PROT_WRITE : 0);
  if (mprotect((void *)lo, hi - lo, prot) != 0)
    lh_die("mprotect(%s) failed on .text", writable ? "rwx" : "rx");
}

/* Rewrite every rel32 call/jmp to `target_addr` inside one of the functions
   named in `allow`.  Returns the number of sites rewritten.

   Only the *allowed callers'* own byte ranges are scanned, not the whole 135 MB
   of `.text`: the callers are named, and `.symtab` gives each one an address
   and a size.  Scanning all of `.text` once per target — which is what this did
   first — cost about 5 G instructions at load, more than doubling a short
   `modelgen` run for no information. */
static int lh_patch_target(const char *what, uintptr_t target_addr,
                           void *hook, lh_allow *allow, size_t nallow) {
  unsigned char *tramp = lh_tramp(hook);
  unsigned char *text = (unsigned char *)(H.base + H.text_addr);
  int            patched = 0;

  for (size_t j = 0; j < nallow; j++) {
    const lh_sym *own = lh_find(allow[j].owner);
    if (!own)
      lh_die("caller %s not found in .symtab", allow[j].owner);
    uintptr_t lo = own->addr, hi = own->addr + own->size;
    if (own->size == 0) hi = lo + 0x10000; /* no size recorded: bounded guess */
    if (lo < H.text_addr || hi > H.text_addr + H.text_size)
      lh_die("caller %s is not inside .text", allow[j].owner);
    for (uintptr_t a = lo; a + 5 <= hi; a++) {
      size_t        i = a - H.text_addr;
      unsigned char op = text[i];
      if (op != 0xE8 && op != 0xE9) continue;
      int32_t disp;
      memcpy(&disp, text + i + 1, 4);
      if (a + 5 + (intptr_t)disp != target_addr) continue;
      intptr_t nd = (intptr_t)tramp - (intptr_t)(text + i + 5);
      if (nd < INT32_MIN || nd > INT32_MAX)
        lh_die("trampoline out of rel32 range for %s", allow[j].label);
      int32_t nd32 = (int32_t)nd;
      memcpy(text + i + 1, &nd32, 4);
      /* read back */
      int32_t chk;
      memcpy(&chk, text + i + 1, 4);
      if (chk != nd32) lh_die("call-site write did not stick at %p", text + i);
      allow[j].found++;
      patched++;
      lh_say("[levelhack]   %-12s <- %s  (%s at %p)\n", what, allow[j].label,
             op == 0xE8 ? "call" : "jmp", (void *)(text + i));
    }
  }
  return patched;
}

/* ================================================================== */
/* Exit report.                                                       */
/* ================================================================== */

static void lh_report(void) {
  if (!lh_active) return;
  lh_say("\n[levelhack] level-comparison census for this process\n");
  lh_say("[levelhack]   is_equivalent: %lu calls\n", C.equiv_calls);
  lh_say("[levelhack]     accepted by the STOCK kernel        : %lu\n",
         C.equiv_stock_true);
  lh_say("[levelhack]     accepted ONLY under interposition   : %lu\n",
         C.equiv_escape);
  lh_say("[levelhack]     rejected by both                    : %lu"
         "   (%lu of them: procedure had no opinion)\n",
         C.equiv_both_false, C.equiv_unknown);
  lh_say("[levelhack]   is_geq:        %lu calls\n", C.geq_calls);
  lh_say("[levelhack]     accepted by the STOCK kernel        : %lu\n",
         C.geq_stock_true);
  lh_say("[levelhack]     accepted ONLY under interposition   : %lu\n",
         C.geq_escape);
  lh_say("[levelhack]     rejected by both                    : %lu"
         "   (%lu of them: procedure had no opinion)\n",
         C.geq_both_false, C.geq_unknown);
  if (lh_meta) {
    lh_say("[levelhack]   Lean.Meta.isLevelDefEq (ELABORATOR, not the kernel): "
           "%lu calls\n", C.meta_calls);
    lh_say("[levelhack]     accepted by stock Lean.Meta          : %lu\n",
           C.meta_stock_true);
    lh_say("[levelhack]     accepted ONLY under interposition    : %lu\n",
           C.meta_escape);
    lh_say("[levelhack]     rejected by both                     : %lu\n",
           C.meta_both_false);
    if (C.meta_unflippable)
      lh_say("[levelhack]     NOT flipped, result object shared    : %lu\n",
             C.meta_unflippable);
  }
  if (C.equiv_escape == 0 && C.geq_escape == 0 && C.meta_escape == 0)
    lh_say("[levelhack]   NO ESCAPES: every level comparison in this run was "
           "decided by stock Lean.\n");
  else
    lh_say("[levelhack]   ESCAPES PRESENT: this run is NOT a stock-kernel "
           "result.  Anything it accepted\n"
           "[levelhack]   may be something Lean's own kernel refuses.\n");
}

/* ================================================================== */
/* The constructor: find, plan, patch, announce.                      */
/* ================================================================== */

__attribute__((constructor)) static void lh_init(void) {
  const char *off = getenv("MODELGEN_LEVELHACK");
  if (off && strcmp(off, "off") == 0) {
    lh_say("[levelhack] MODELGEN_LEVELHACK=off: loaded, patched nothing.\n");
    return;
  }
  lh_trace = getenv("MODELGEN_LEVELHACK_TRACE") != NULL;
  { const char *m = getenv("MODELGEN_LEVELHACK_META");
    if (m && strcmp(m, "0") == 0) lh_meta = 0; }

  lh_load_symbols();

  /* Is this a Lean process at all?  Under LD_PRELOAD this constructor runs in
     whatever the shell launched — `timeout`, `env`, `sh` — and killing those
     helps nobody.  A host with no Lean runtime is not a host that was asked to
     be patched, so it is left alone with a note.  A host that *is* Lean and
     still cannot be patched is the loud case, and falls through to lh_die. */
  if (!lh_find("lean_initialize_runtime_module") &&
      !dlsym(RTLD_DEFAULT, "lean_initialize_runtime_module")) {
    lh_say("[levelhack] not a Lean process (%s); patched nothing.\n",
           program_invocation_short_name);
    return;
  }

  const lh_sym *se = lh_find("_ZN4lean13is_equivalentERKNS_5levelES2_");
  const lh_sym *sg = lh_find("_ZN4lean6is_geqERKNS_5levelES2_");
  if (!se)
    lh_die("lean::is_equivalent not found in .symtab of the host executable");
  if (!sg) lh_die("lean::is_geq not found in .symtab of the host executable");

  orig_is_equivalent = (uint8_t (*)(void **, void **))(H.base + se->addr);
  orig_is_geq = (uint8_t (*)(void **, void **))(H.base + sg->addr);
  lean_name_eq_p = (uint8_t (*)(void *, void *))lh_host("lean_name_eq");

  lh_say("[levelhack] ==================================================="
         "==============\n");
  lh_say("[levelhack] INTERPOSING ON LEAN'S KERNEL LEVEL COMPARISON.\n");
  lh_say("[levelhack] This process's Lean kernel is NOT stock.  Anything it\n"
         "[levelhack] accepts under an escape is NOT 'checked by Lean's "
         "kernel'.\n");
  lh_say("[levelhack]   host base           %p\n", (void *)H.base);
  lh_say("[levelhack]   lean::is_equivalent %p\n", (void *)orig_is_equivalent);
  lh_say("[levelhack]   lean::is_geq        %p\n", (void *)orig_is_geq);
  lh_say("[levelhack]   rewriting call sites:\n");

  lh_tramp_alloc_page(H.base + H.text_addr + H.text_size);
  lh_mprotect_text(1);
  int ne = lh_patch_target("is_equivalent", se->addr, (void *)hook_is_equivalent,
                           allow_equiv,
                           sizeof(allow_equiv) / sizeof(allow_equiv[0]));
  int ng = lh_patch_target("is_geq", sg->addr, (void *)hook_is_geq, allow_geq,
                           sizeof(allow_geq) / sizeof(allow_geq[0]));
  int nm = 0;
  if (lh_meta) {
    const lh_sym *sm = lh_find("lean_is_level_def_eq");
    if (!sm)
      lh_die("Lean.Meta.isLevelDefEq (lean_is_level_def_eq) not found; set "
             "MODELGEN_LEVELHACK_META=0 to run kernel-only");
    orig_meta_ldeq = (lh_meta_fn)(H.base + sm->addr);
    nm = lh_patch_target("meta_defeq", sm->addr, (void *)hook_meta_ldeq,
                         allow_meta,
                         sizeof(allow_meta) / sizeof(allow_meta[0]));
  }
  lh_mprotect_text(0);

  for (size_t j = 0; j < sizeof(allow_equiv) / sizeof(allow_equiv[0]); j++)
    if (!allow_equiv[j].found)
      lh_die("expected call site not found: %s -> lean::is_equivalent",
             allow_equiv[j].label);
  for (size_t j = 0; j < sizeof(allow_geq) / sizeof(allow_geq[0]); j++)
    if (!allow_geq[j].found)
      lh_die("expected call site not found: %s -> lean::is_geq",
             allow_geq[j].label);
  if (lh_meta)
    for (size_t j = 0; j < sizeof(allow_meta) / sizeof(allow_meta[0]); j++)
      if (!allow_meta[j].found)
        lh_die("expected call site not found: %s -> lean_is_level_def_eq",
               allow_meta[j].label);

  /* Do not inherit into children, now that this process is patched.
     `Lean.findSysroot` shells out to `lean --print-libdir`, and the shipped
     `lean` links a *stripped* libleanshared.so, so this library would
     (correctly) refuse to run there and take the child down with it.  Done
     here and not at entry, so that an `LD_PRELOAD` line that reaches this
     process through a `timeout` or an `env` still reaches this process. */
  unsetenv("LD_PRELOAD");

  lh_say("[levelhack]   %d + %d + %d call sites rewritten.\n", ne, ng, nm);
  lh_say("[levelhack] ==================================================="
         "==============\n");
  lh_active = 1;
  atexit(lh_report);
}

/* ================================================================== */
/* Lean-object construction, for the self-test and the fuzz.          */
/* ================================================================== */

static void *(*p_mk_zero)(void);
static void *(*p_mk_succ)(void *);
static void *(*p_mk_max)(void *, void *);
static void *(*p_mk_imax)(void *, void *);
static void *(*p_mk_param)(void *);
static void *(*p_mk_string)(const char *);
static void *(*p_name_mk_string)(void *, void *);
static void  (*p_dec_ref_cold)(void *);
static uint8_t (*p_level_eqv)(void *, void *);

static void lo_inc(void *o) {
  if (LO_IS_SCALAR(o)) return;
  int *rc = (int *)o;
  if (*rc > 0) (*rc)++;
}
static void lo_dec(void *o) {
  if (LO_IS_SCALAR(o)) return;
  int *rc = (int *)o;
  if (*rc > 1) { (*rc)--; return; }
  if (*rc != 0 && p_dec_ref_cold) p_dec_ref_cold(o);
}

static int lh_resolve_runtime(void) {
  p_mk_zero = lh_host("lean_level_mk_zero");
  p_mk_succ = lh_host("lean_level_mk_succ");
  p_mk_max = lh_host("lean_level_mk_max");
  p_mk_imax = lh_host("lean_level_mk_imax");
  p_mk_param = lh_host("lean_level_mk_param");
  p_mk_string = lh_host("lean_mk_string");
  p_name_mk_string = lh_host("lean_name_mk_string");
  p_dec_ref_cold = lh_host("lean_dec_ref_cold");
  p_level_eqv = lh_host("lean_level_eqv");
  return p_mk_zero && p_mk_succ && p_mk_max && p_mk_imax && p_mk_param &&
         p_mk_string && p_name_mk_string && p_dec_ref_cold && p_level_eqv;
}

static void *lh_mk_name(const char *s) {
  void *anon = (void *)(uintptr_t)1; /* Name.anonymous is lean_box(0) */
  return p_name_mk_string(anon, p_mk_string(s));
}

/* Build the Lean level denoted by AST node `n`, using `names[i]` for var i. */
static void *lh_to_lean(const la_arena *ar, int32_t n, void **names) {
  switch (ar->nodes[n].kind) {
    case LA_ZERO:
      return p_mk_zero();
    case LA_SUCC:
      return p_mk_succ(lh_to_lean(ar, ar->nodes[n].a, names));
    case LA_MAX:
      return p_mk_max(lh_to_lean(ar, ar->nodes[n].a, names),
                      lh_to_lean(ar, ar->nodes[n].b, names));
    case LA_IMAX:
      return p_mk_imax(lh_to_lean(ar, ar->nodes[n].a, names),
                       lh_to_lean(ar, ar->nodes[n].b, names));
    case LA_VAR: {
      void *nm = names[ar->nodes[n].var];
      lo_inc(nm);
      return p_mk_param(nm);
    }
  }
  return p_mk_zero();
}

/* ================================================================== */
/* Self-test: an observed behaviour change, not a return code.        */
/* ================================================================== */

static void lh_selftest(void) {
  if (!lh_resolve_runtime())
    lh_die("could not resolve Lean's level constructors via dlsym; the host "
           "does not export the C API this self-test needs");

  void *nu = lh_mk_name("u"), *nv = lh_mk_name("v");
  la_node  storage[4096];
  la_arena ar;
  la_arena_init(&ar, storage, 4096);
  void *names[2] = {nu, nv};

  /* MODELGEN.md §8.6's witness:
       max 1 (imax (imax u v) v) (max 1 u v)   ~   max 1 u v
     equal at every assignment; Lean's normaliser says no. */
  int32_t u = la_mk_var(&ar, 0), v = la_mk_var(&ar, 1);
  int32_t one = la_mk_succ(&ar, la_mk_zero(&ar));
  int32_t rhs = la_mk_max(&ar, la_mk_max(&ar, one, u), v);
  int32_t lhs = la_mk_max(
      &ar, la_mk_max(&ar, one, la_mk_imax(&ar, la_mk_imax(&ar, u, v), v)), rhs);

  void *L1 = lh_to_lean(&ar, lhs, names), *R1 = lh_to_lean(&ar, rhs, names);
  void *L2 = lh_to_lean(&ar, lhs, names), *R2 = lh_to_lean(&ar, rhs, names);

  void *pl = L1, *pr = R1;
  uint8_t stock = orig_is_equivalent(&pl, &pr);
  uint8_t viaPatchedCallSite = p_level_eqv(L2, R2);

  lo_dec(L1); lo_dec(R1); lo_dec(L2); lo_dec(R2);
  lo_dec(nu); lo_dec(nv);

  if (stock != 0)
    lh_die("self-test precondition failed: the STOCK kernel already accepts "
           "the §8.6 witness.\n        Either the witness is wrong or this is "
           "not the Lean this was written against.");
  if (viaPatchedCallSite != 1)
    lh_die("self-test FAILED: the patched call site in lean_level_eqv still "
           "returns the stock answer.\n        The rewrite did not take.  "
           "Nothing in this run is what it claims to be.");

  lh_say("[levelhack] self-test PASSED by observed behaviour change:\n"
         "[levelhack]   max 1 (imax (imax u v) v) (max 1 u v)  ~  max 1 u v\n"
         "[levelhack]   lean::is_equivalent (untouched body, called directly): "
         "false\n"
         "[levelhack]   lean_level_eqv      (patched call site)              : "
         "true\n");
}

/* ================================================================== */
/* The fuzz.                                                          */
/* ================================================================== */

static uint64_t lh_rng_s = 0x9E3779B97F4A7C15ULL;
static uint32_t lh_rng(void) {
  lh_rng_s ^= lh_rng_s << 13;
  lh_rng_s ^= lh_rng_s >> 7;
  lh_rng_s ^= lh_rng_s << 17;
  return (uint32_t)(lh_rng_s >> 32);
}

#define FUZZ_MAX_VARS 6

static int lh_fuzz_vars = 3;
/* Widest assignment used by the "wide" oracle; the narrow one is always 0..4,
   which is the oracle MODELGEN.md §8.6 recorded.  Chosen so that the wide
   oracle stays around a couple of thousand points per pair whatever the
   variable count is. */
static int lh_fuzz_wide = 12;

static int32_t lh_gen(la_arena *ar, int depth) {
  if (depth == 0) {
    unsigned r = lh_rng() % (unsigned)(lh_fuzz_vars + 1);
    if (r == 0) return la_mk_zero(ar);
    return la_mk_var(ar, (int32_t)(r - 1));
  }
  unsigned r = lh_rng() % 6;
  switch (r) {
    case 0: return la_mk_zero(ar);
    case 1: return la_mk_var(ar, (int32_t)(lh_rng() % (unsigned)lh_fuzz_vars));
    case 2: return la_mk_succ(ar, lh_gen(ar, depth - 1));
    case 3: return la_mk_max(ar, lh_gen(ar, depth - 1), lh_gen(ar, depth - 1));
    default:
      return la_mk_imax(ar, lh_gen(ar, depth - 1), lh_gen(ar, depth - 1));
  }
}

static int lh_fuzz_depth = 4;

static void lh_fuzz(unsigned long n) {
  if (!lh_resolve_runtime()) lh_die("fuzz: cannot resolve Lean's level API");
  static const char *vn[FUZZ_MAX_VARS] = {"u", "v", "w", "x", "y", "z"};
  void *names[FUZZ_MAX_VARS];
  for (int k = 0; k < lh_fuzz_vars; k++) names[k] = lh_mk_name(vn[k]);

  /* `4` suffix: the §8.6 oracle, every assignment in 0..4.
     `w` suffix: the same over 0..12, which is what everything is *scored*
     against, because it strictly refutes more.  Both are bounded oracles and
     neither proves anything positive. */
  unsigned long sem4 = 0, semw = 0, narrow_wrong_eq = 0;
  unsigned long lean_miss = 0, lean_false_accept = 0;
  unsigned long mine_miss = 0, mine_false_accept = 0, mine_unknown = 0;
  unsigned long g_sem4 = 0, g_semw = 0, narrow_wrong_ge = 0;
  unsigned long g_lean_miss = 0, g_lean_false_accept = 0;
  unsigned long g_mine_miss = 0, g_mine_false_accept = 0, g_mine_unknown = 0;

  la_node *storage = malloc(sizeof(la_node) * LA_ARENA_CAP);
  if (!storage) lh_die("fuzz: out of memory");

  for (unsigned long i = 0; i < n; i++) {
    la_arena ar;
    la_arena_init(&ar, storage, LA_ARENA_CAP);
    int32_t a = lh_gen(&ar, lh_fuzz_depth), b = lh_gen(&ar, lh_fuzz_depth);
    if (a < 0 || b < 0) continue;
    int32_t inputs_end = ar.len;

    /* Two bounded semantic oracles.  Note the asymmetry the report leans on:
       an oracle that finds a *counterexample* has refuted the pair for good,
       but an oracle that finds none has proved nothing.  So FALSE ACCEPTS is
       an exact count against whichever oracle refuted, and "missed" is only
       an upper bound.  The wide oracle exists because the narrow one
       over-reports `>=`: `4 >= w` holds on 0..4 and fails at 5. */
    int eq4 = 1, ge4 = 1, eq = 1, ge = 1;
    uint32_t rho[LA_MAX_VARS];
    for (int k = 0; k < lh_fuzz_vars; k++) rho[k] = 0;
    for (;;) {
      uint32_t x = la_eval(&ar, a, rho), y = la_eval(&ar, b, rho);
      int narrow = 1;
      for (int k = 0; k < lh_fuzz_vars; k++) if (rho[k] > 4) narrow = 0;
      if (x != y) { eq = 0; if (narrow) eq4 = 0; }
      if (x < y)  { ge = 0; if (narrow) ge4 = 0; }
      int k = 0;
      for (; k < lh_fuzz_vars; k++) {
        if (rho[k] < (uint32_t)lh_fuzz_wide) { rho[k]++; break; }
        rho[k] = 0;
      }
      if (k == lh_fuzz_vars) break;
    }

    /* stock Lean, through the untouched function body */
    void *la = lh_to_lean(&ar, a, names), *lb = lh_to_lean(&ar, b, names);
    void *pa = la, *pb = lb;
    uint8_t lean_eq = orig_is_equivalent(&pa, &pb);
    pa = la; pb = lb;
    uint8_t lean_ge = orig_is_geq(&pa, &pb);
    lo_dec(la);
    lo_dec(lb);

    /* the replacement */
    ar.len = inputs_end;
    ar.overflow = 0;
    la_result mine_eq = la_equiv(&ar, a, b);
    ar.len = inputs_end;
    ar.overflow = 0;
    la_result mine_ge = la_geq(&ar, a, b);

    if (eq4) sem4++;
    if (eq) semw++;
    if (eq4 && !eq) narrow_wrong_eq++;
    if (eq && !lean_eq) lean_miss++;
    if (!eq && lean_eq) lean_false_accept++;
    if (mine_eq == LA_UNKNOWN) mine_unknown++;
    else {
      if (eq && mine_eq == LA_FALSE) mine_miss++;
      if (!eq && mine_eq == LA_TRUE) mine_false_accept++;
    }

    if (ge4) g_sem4++;
    if (ge) g_semw++;
    if (ge4 && !ge) narrow_wrong_ge++;
    if (ge && !lean_ge) g_lean_miss++;
    if (!ge && lean_ge) g_lean_false_accept++;
    if (mine_ge == LA_UNKNOWN) g_mine_unknown++;
    else {
      if (ge && mine_ge == LA_FALSE) g_mine_miss++;
      if (!ge && mine_ge == LA_TRUE) g_mine_false_accept++;
    }
  }

  lh_say("\n[levelhack] FUZZ: %lu pairs, depth-%d random levels, %d variables.\n"
         "[levelhack]   narrow oracle = every assignment in 0..4      (§8.6's)\n"
         "[levelhack]   wide oracle   = every assignment in 0..%-2d     <- "
         "scored against\n",
         n, lh_fuzz_depth, lh_fuzz_vars, lh_fuzz_wide);
  lh_say("[levelhack] --- equivalence ---------------------------------------"
         "----\n");
  lh_say("[levelhack]   equal on 0..4 / on 0..12                : %lu / %lu"
         "   (narrow oracle wrong %lu times)\n",
         sem4, semw, narrow_wrong_eq);
  lh_say("[levelhack]   lean::is_equivalent  missed (sem yes, said no): %lu\n",
         lean_miss);
  lh_say("[levelhack]   lean::is_equivalent  FALSE ACCEPTS            : %lu\n",
         lean_false_accept);
  lh_say("[levelhack]   replacement          missed (sem yes, said no): %lu\n",
         mine_miss);
  lh_say("[levelhack]   replacement          FALSE ACCEPTS            : %lu\n",
         mine_false_accept);
  lh_say("[levelhack]   replacement          no opinion (LA_UNKNOWN)  : %lu\n",
         mine_unknown);
  lh_say("[levelhack] --- >= ------------------------------------------------"
         "----\n");
  lh_say("[levelhack]   >= on 0..4 / on 0..12                   : %lu / %lu"
         "   (narrow oracle wrong %lu times)\n",
         g_sem4, g_semw, narrow_wrong_ge);
  lh_say("[levelhack]   lean::is_geq         missed                   : %lu\n",
         g_lean_miss);
  lh_say("[levelhack]   lean::is_geq         FALSE ACCEPTS            : %lu\n",
         g_lean_false_accept);
  lh_say("[levelhack]   replacement          missed                   : %lu\n",
         g_mine_miss);
  lh_say("[levelhack]   replacement          FALSE ACCEPTS            : %lu\n",
         g_mine_false_accept);
  lh_say("[levelhack]   replacement          no opinion (LA_UNKNOWN)  : %lu\n",
         g_mine_unknown);
  lh_say("[levelhack] A bounded oracle is a measurement, not a completeness "
         "proof.  What it does\n"
         "[levelhack] establish exactly is the FALSE ACCEPTS line: a "
         "counterexample found is a\n"
         "[levelhack] counterexample.  The 'missed' lines are upper bounds "
         "only.\n");
  free(storage);
}

/* ================================================================== */
/* First-call hook: run the checks once the Lean runtime exists.      */
/* ================================================================== */

static int lh_checks_state = 0; /* 0 not run, 1 running, 2 done */

static int lh_in_selftest(void) {
  return __atomic_load_n(&lh_checks_state, __ATOMIC_ACQUIRE) == 1;
}

static void lh_first_call_checks(void) {
  if (__atomic_load_n(&lh_checks_state, __ATOMIC_ACQUIRE) == 2) return;
  int expected = 0;
  if (!__atomic_compare_exchange_n(&lh_checks_state, &expected, 1, 0,
                                   __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE))
    return; /* re-entrant (the self-test itself) or another thread */
  lh_selftest();
  const char *f = getenv("MODELGEN_LEVELHACK_FUZZ");
  if (f) {
    unsigned long n = strtoul(f, NULL, 10);
    const char *d = getenv("MODELGEN_LEVELHACK_FUZZ_DEPTH");
    if (d) lh_fuzz_depth = (int)strtol(d, NULL, 10);
    const char *sd = getenv("MODELGEN_LEVELHACK_FUZZ_SEED");
    if (sd) lh_rng_s = strtoull(sd, NULL, 10) | 1ULL;
    const char *nv = getenv("MODELGEN_LEVELHACK_FUZZ_VARS");
    if (nv) {
      lh_fuzz_vars = (int)strtol(nv, NULL, 10);
      if (lh_fuzz_vars < 1) lh_fuzz_vars = 1;
      if (lh_fuzz_vars > FUZZ_MAX_VARS) lh_fuzz_vars = FUZZ_MAX_VARS;
      /* keep the wide oracle near 2000 points per pair */
      lh_fuzz_wide = 12;
      while (lh_fuzz_wide > 4) {
        double pts = 1.0;
        for (int k = 0; k < lh_fuzz_vars; k++) pts *= (lh_fuzz_wide + 1);
        if (pts <= 4000.0) break;
        lh_fuzz_wide--;
      }
    }
    /* Override the wide oracle's range explicitly.  Needed to check that a
       "missed" count at four or more variables is the oracle being too narrow
       (as it demonstrably is at three) rather than a gap in the procedure. */
    const char *wd = getenv("MODELGEN_LEVELHACK_FUZZ_WIDE");
    if (wd) lh_fuzz_wide = (int)strtol(wd, NULL, 10);
    if (n) {
      lh_fuzz(n);
      lh_say("[levelhack] fuzz complete; exiting (this is a measurement "
             "mode).\n");
      _exit(0);
    }
  }
  __atomic_store_n(&lh_checks_state, 2, __ATOMIC_RELEASE);
}
