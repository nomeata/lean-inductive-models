/* fuzz_ref.c — the §8.6 fuzz, detached from the interposer.

   `interpose.c`'s `lh_fuzz` scores three things at once: stock Lean's
   `is_equivalent`, the replacement, and a bounded semantic oracle.  Scoring
   stock Lean is what ties it to a loaded `.so` and a resolved Lean runtime.

   The planner does not interpose — it calls a *port* of the procedure from
   Lean directly (`Modelgen/LevelAlgebra.lean`) — so the port's fuzz needs the
   other two legs and not the first.  This driver is those two legs in plain
   C, over exactly the same RNG, the same generator, and the same oracle, so
   that `LevelFuzz.lean` can be run on the identical pair stream and the two
   verdict streams compared pair for pair.  A digest of the verdict stream is
   printed for precisely that comparison.

   Build: see build.sh (`fuzz-ref` target).  Links only level_algebra.c. */

#include "level_algebra.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---- the generator, verbatim from interpose.c ---------------------- */

static uint64_t lh_rng_s = 0x9E3779B97F4A7C15ULL;
static uint32_t lh_rng(void) {
  lh_rng_s ^= lh_rng_s << 13;
  lh_rng_s ^= lh_rng_s >> 7;
  lh_rng_s ^= lh_rng_s << 17;
  return (uint32_t)(lh_rng_s >> 32);
}

static int fuzz_vars = 3;
static int fuzz_depth = 4;
static int fuzz_wide = 12;

static int32_t lh_gen(la_arena *ar, int depth) {
  if (depth == 0) {
    unsigned r = lh_rng() % (unsigned)(fuzz_vars + 1);
    if (r == 0) return la_mk_zero(ar);
    return la_mk_var(ar, (int32_t)(r - 1));
  }
  unsigned r = lh_rng() % 6;
  /* NB: the two recursive calls are sequenced into locals, where interpose.c
     leaves them as sibling arguments.  C does not fix the evaluation order of
     function arguments, so the sibling form makes the pair stream a property
     of the compiler; the port has to reproduce the stream exactly for the
     digest comparison to mean anything.  Left-to-right, explicitly.  The
     family of pairs generated is the same either way. */
  switch (r) {
    case 0: return la_mk_zero(ar);
    case 1: return la_mk_var(ar, (int32_t)(lh_rng() % (unsigned)fuzz_vars));
    case 2: return la_mk_succ(ar, lh_gen(ar, depth - 1));
    case 3: {
      int32_t l = lh_gen(ar, depth - 1);
      int32_t r2 = lh_gen(ar, depth - 1);
      return la_mk_max(ar, l, r2);
    }
    default: {
      int32_t l = lh_gen(ar, depth - 1);
      int32_t r2 = lh_gen(ar, depth - 1);
      return la_mk_imax(ar, l, r2);
    }
  }
}

/* FNV-1a over the verdict stream, so the port can be compared to this
   reference without shipping 6 M verdicts between the two. */
static uint64_t digest = 1469598103934665603ULL;
static void dig(uint8_t b) {
  digest ^= b;
  digest *= 1099511628211ULL;
}

int main(int argc, char **argv) {
  unsigned long n = 1000000;
  if (argc > 1) n = strtoul(argv[1], NULL, 10);
  if (argc > 2) fuzz_depth = (int)strtol(argv[2], NULL, 10);
  if (argc > 3) fuzz_vars = (int)strtol(argv[3], NULL, 10);
  if (argc > 4) fuzz_wide = (int)strtol(argv[4], NULL, 10);

  unsigned long sem4 = 0, semw = 0, narrow_wrong_eq = 0;
  unsigned long mine_miss = 0, mine_false_accept = 0, mine_unknown = 0;
  unsigned long g_semw = 0;
  unsigned long g_mine_miss = 0, g_mine_false_accept = 0, g_mine_unknown = 0;

  la_node *storage = malloc(sizeof(la_node) * LA_ARENA_CAP);
  if (!storage) return fprintf(stderr, "out of memory\n"), 1;

  for (unsigned long i = 0; i < n; i++) {
    la_arena ar;
    la_arena_init(&ar, storage, LA_ARENA_CAP);
    int32_t a = lh_gen(&ar, fuzz_depth), b = lh_gen(&ar, fuzz_depth);
    if (a < 0 || b < 0) continue;
    int32_t inputs_end = ar.len;

    int eq4 = 1, eq = 1, ge = 1;
    uint32_t rho[LA_MAX_VARS];
    for (int k = 0; k < fuzz_vars; k++) rho[k] = 0;
    for (;;) {
      uint32_t x = la_eval(&ar, a, rho), y = la_eval(&ar, b, rho);
      int narrow = 1;
      for (int k = 0; k < fuzz_vars; k++) if (rho[k] > 4) narrow = 0;
      if (x != y) { eq = 0; if (narrow) eq4 = 0; }
      if (x < y) ge = 0;
      int k = 0;
      for (; k < fuzz_vars; k++) {
        if (rho[k] < (uint32_t)fuzz_wide) { rho[k]++; break; }
        rho[k] = 0;
      }
      if (k == fuzz_vars) break;
    }

    ar.len = inputs_end; ar.overflow = 0;
    la_result mine_eq = la_equiv(&ar, a, b);
    ar.len = inputs_end; ar.overflow = 0;
    la_result mine_ge = la_geq(&ar, a, b);

    dig((uint8_t)mine_eq);
    dig((uint8_t)mine_ge);

    if (eq4) sem4++;
    if (eq) semw++;
    if (eq4 && !eq) narrow_wrong_eq++;
    if (mine_eq == LA_UNKNOWN) mine_unknown++;
    else {
      if (eq && mine_eq == LA_FALSE) mine_miss++;
      if (!eq && mine_eq == LA_TRUE) mine_false_accept++;
    }
    if (ge) g_semw++;
    if (mine_ge == LA_UNKNOWN) g_mine_unknown++;
    else {
      if (ge && mine_ge == LA_FALSE) g_mine_miss++;
      if (!ge && mine_ge == LA_TRUE) g_mine_false_accept++;
    }
  }

  printf("C   pairs=%lu depth=%d vars=%d wide=%d\n", n, fuzz_depth, fuzz_vars,
         fuzz_wide);
  printf("C   eq: sem(0..4)=%lu sem(wide)=%lu narrow_wrong=%lu\n", sem4, semw,
         narrow_wrong_eq);
  printf("C   eq: missed=%lu FALSE_ACCEPTS=%lu unknown=%lu\n", mine_miss,
         mine_false_accept, mine_unknown);
  printf("C   ge: sem(wide)=%lu missed=%lu FALSE_ACCEPTS=%lu unknown=%lu\n",
         g_semw, g_mine_miss, g_mine_false_accept, g_mine_unknown);
  printf("C   digest=%016llx\n", (unsigned long long)digest);
  free(storage);
  return 0;
}
