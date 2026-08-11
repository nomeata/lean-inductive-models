/*
  level_algebra.h — a complete decision procedure for Lean's universe-level
  algebra, over a private AST.

  # What this is

  Lean's universe levels are the free algebra

      l ::= 0 | succ l | max l l | imax l l | x            (x a variable)

  with the semantics, for an assignment rho : Var -> Nat,

      [0]      = 0
      [succ l] = [l] + 1
      [max u v]  = max([u], [v])
      [imax u v] = if [v] = 0 then 0 else max([u], [v])
      [x]      = rho(x)

  `la_equiv` decides `forall rho. [u] = [v]` and `la_geq` decides
  `forall rho. [u] >= [v]`.  Both are *decision procedures*: they are exact on
  this algebra, subject only to the resource caps below, which are reported as
  LA_UNKNOWN rather than guessed.

  # Why a decision procedure and not Lean's normaliser

  Lean's kernel compares levels by normalising and testing the normal forms
  structurally (`lean::is_equivalent`).  That is sound but incomplete: a `max`
  does not absorb an `imax` it dominates, so e.g.

      max 1 (imax (imax u v) v) (max 1 u v)   vs   max 1 u v

  are equal at every rho and Lean says no.  MODELGEN.md §8.6 records that
  refusal and the lean4lean cross-check of it.

  # The algorithm

  Two steps, both standard.

  1. *Push `imax` down until its second argument is a variable.*  These four
     rewrites are semantics-preserving (each is checked at every case of
     "is the second argument zero"):

         imax a 0        = 0
         imax a (succ b) = max a (succ b)
         imax a (max b c)  = max (imax a b) (imax a c)
         imax a (imax b c) = imax (max a b) c

  2. *Case-split on the remaining `imax` variables.*  If `imax a x` survives,
     then whether it is `0` depends only on whether `rho(x)` is `0`, so

         u ~ v   iff   u[x:=0] ~ v[x:=0]  and  u[x:=succ x] ~ v[x:=succ x]

     (`x := succ x` is the reparametrisation rho(x) = 1 + rho'(x), which is a
     bijection onto the assignments with rho(x) >= 1).  Either substitution
     makes every `imax _ x` reduce away by step 1, and no *new* variable can
     enter second position, so the number of `imax` variables strictly
     decreases and the recursion terminates.

  3. At the leaves no `imax` remains, so the level is a `max` of `x + k` terms
     and a constant.  The canonical form is

         (const k, {x |-> off_x})   meaning   max(k, max_x (rho(x) + off_x))

     with `k` dropped to 0 when some `off_x >= k` (then `k` is redundant,
     since `rho(x) + off_x >= off_x >= k`).  That form is canonical: setting
     all variables to 0 reads off `max(k, max off_x)`, and sending one
     variable to infinity reads off its presence and offset.  So structural
     equality of canonical forms decides `forall rho. [u] = [v]`, and

         u >= v   iff   min_rho [u] >= k_v
                   and  every variable of v occurs in u at an offset >= its
                        offset in v

     decides the inequality.

  # Resource caps -> LA_UNKNOWN, never a guess

  LA_UNKNOWN is returned, and never LA_TRUE, when a cap is hit:

    * more than LA_MAX_VARS distinct variables;
    * more than LA_MAX_SPLITS nested case splits (2^n leaves);
    * arena exhaustion (rewrite 1 duplicates `a` when it distributes).

  A caller must treat LA_UNKNOWN as "no opinion" and fall back.  This is what
  keeps the procedure from ever being *less* sound than the thing it extends.

  # Not a completeness proof

  The argument above is a correctness argument, not a machine-checked proof,
  and the implementation is C.  The evidence that it does not accept a
  semantically false pair is the fuzz in `interpose.c` against a bounded
  oracle (`la_eval`), reported in MODELGEN.md §8.6.  A bounded oracle is a
  measurement, not a proof.
*/

#ifndef MODELGEN_LEVEL_ALGEBRA_H
#define MODELGEN_LEVEL_ALGEBRA_H

#include <stdint.h>

#define LA_MAX_VARS   16
/* At most 2^LA_MAX_SPLITS leaves.  Ten distinct variables in `imax` second
   position in one comparison does not occur in practice; the cap exists so
   that a pathological input degrades to LA_UNKNOWN instead of hanging. */
#define LA_MAX_SPLITS 10
/* 16 bytes per node.  The arena is a bump allocator that is never freed
   within a call, so it must cover every leaf of the case split. */
#define LA_ARENA_CAP  (1 << 18)

/* AST node kinds. */
enum {
  LA_ZERO = 0,
  LA_SUCC = 1,
  LA_MAX  = 2,
  LA_IMAX = 3,
  LA_VAR  = 4
};

typedef struct {
  int32_t kind;
  int32_t var; /* LA_VAR only */
  int32_t a;   /* LA_SUCC / LA_MAX / LA_IMAX */
  int32_t b;   /* LA_MAX / LA_IMAX */
} la_node;

/* A bump arena of AST nodes.  Node index -1 means "failed" (cap hit). */
typedef struct {
  la_node *nodes;
  int32_t  len;
  int32_t  cap;
  int32_t  nvars;
  int      overflow;
} la_arena;

typedef enum { LA_FALSE = 0, LA_TRUE = 1, LA_UNKNOWN = 2 } la_result;

void    la_arena_init(la_arena *ar, la_node *storage, int32_t cap);
int32_t la_mk_zero(la_arena *ar);
int32_t la_mk_succ(la_arena *ar, int32_t a);
int32_t la_mk_max(la_arena *ar, int32_t a, int32_t b);
int32_t la_mk_imax(la_arena *ar, int32_t a, int32_t b);
int32_t la_mk_var(la_arena *ar, int32_t v);

/* The decision procedures.  `u`, `v` are node indices in `ar`.
   `ar` is used as scratch and will grow. */
la_result la_equiv(la_arena *ar, int32_t u, int32_t v);
la_result la_geq(la_arena *ar, int32_t u, int32_t v);

/* The semantic oracle: evaluate under an explicit assignment.  Used by the
   fuzz, and by nothing else. */
uint32_t la_eval(const la_arena *ar, int32_t n, const uint32_t *rho);

/* Render to a buffer, for the escape trace.  Variables print as the strings
   in `varnames` when that is non-NULL, else as `?i`. */
void la_print(const la_arena *ar, int32_t n, char *buf, int32_t bufsz,
              const char *const *varnames);

#endif
