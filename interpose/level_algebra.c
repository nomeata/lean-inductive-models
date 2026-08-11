/* level_algebra.c — implementation of the decision procedure documented in
   level_algebra.h.  Read that header first; it carries the correctness
   argument and the meaning of LA_UNKNOWN. */

#include "level_algebra.h"

#include <stdio.h>
#include <string.h>

void la_arena_init(la_arena *ar, la_node *storage, int32_t cap) {
  ar->nodes = storage;
  ar->len = 0;
  ar->cap = cap;
  ar->nvars = 0;
  ar->overflow = 0;
}

static int32_t la_alloc(la_arena *ar, int32_t kind, int32_t var, int32_t a,
                        int32_t b) {
  if (a < 0 || b < 0) return -1;
  if (ar->len >= ar->cap) {
    ar->overflow = 1;
    return -1;
  }
  int32_t i = ar->len++;
  ar->nodes[i].kind = kind;
  ar->nodes[i].var = var;
  ar->nodes[i].a = a;
  ar->nodes[i].b = b;
  return i;
}

int32_t la_mk_zero(la_arena *ar) { return la_alloc(ar, LA_ZERO, -1, 0, 0); }
int32_t la_mk_succ(la_arena *ar, int32_t a) {
  return la_alloc(ar, LA_SUCC, -1, a, 0);
}
int32_t la_mk_max(la_arena *ar, int32_t a, int32_t b) {
  return la_alloc(ar, LA_MAX, -1, a, b);
}
int32_t la_mk_imax(la_arena *ar, int32_t a, int32_t b) {
  return la_alloc(ar, LA_IMAX, -1, a, b);
}
int32_t la_mk_var(la_arena *ar, int32_t v) {
  if (v < 0 || v >= LA_MAX_VARS) {
    ar->overflow = 1;
    return -1;
  }
  if (v >= ar->nvars) ar->nvars = v + 1;
  return la_alloc(ar, LA_VAR, v, 0, 0);
}

/* ------------------------------------------------------------------ */
/* Step 1: push `imax` down until its second argument is a variable.   */
/* ------------------------------------------------------------------ */

static int32_t la_imax_smart(la_arena *ar, int32_t a, int32_t b);

static int32_t la_simp(la_arena *ar, int32_t n) {
  if (n < 0) return -1;
  switch (ar->nodes[n].kind) {
    case LA_ZERO:
    case LA_VAR:
      return n;
    case LA_SUCC:
      return la_mk_succ(ar, la_simp(ar, ar->nodes[n].a));
    case LA_MAX:
      return la_mk_max(ar, la_simp(ar, ar->nodes[n].a),
                       la_simp(ar, ar->nodes[n].b));
    case LA_IMAX: {
      int32_t a = la_simp(ar, ar->nodes[n].a);
      int32_t b = la_simp(ar, ar->nodes[n].b);
      return la_imax_smart(ar, a, b);
    }
    default:
      return -1;
  }
}

/* `b` is already simplified: it is ZERO, SUCC, MAX, VAR, or an IMAX whose own
   second argument is a VAR. */
static int32_t la_imax_smart(la_arena *ar, int32_t a, int32_t b) {
  if (a < 0 || b < 0) return -1;
  switch (ar->nodes[b].kind) {
    case LA_ZERO:
      /* imax a 0 = 0 */
      return la_mk_zero(ar);
    case LA_SUCC:
      /* imax a (succ b) = max a (succ b) */
      return la_mk_max(ar, a, b);
    case LA_MAX: {
      /* imax a (max c d) = max (imax a c) (imax a d) */
      int32_t c = ar->nodes[b].a, d = ar->nodes[b].b;
      int32_t l = la_imax_smart(ar, a, c);
      int32_t r = la_imax_smart(ar, a, d);
      return la_mk_max(ar, l, r);
    }
    case LA_IMAX: {
      /* imax a (imax c d) = imax (max a c) d */
      int32_t c = ar->nodes[b].a, d = ar->nodes[b].b;
      return la_imax_smart(ar, la_mk_max(ar, a, c), d);
    }
    case LA_VAR:
      return la_mk_imax(ar, a, b);
    default:
      return -1;
  }
}

/* First variable occurring as the second argument of an `imax`, or -1. */
static int32_t la_imax_var(const la_arena *ar, int32_t n) {
  if (n < 0) return -1;
  switch (ar->nodes[n].kind) {
    case LA_ZERO:
    case LA_VAR:
      return -1;
    case LA_SUCC:
      return la_imax_var(ar, ar->nodes[n].a);
    case LA_MAX: {
      int32_t x = la_imax_var(ar, ar->nodes[n].a);
      return x >= 0 ? x : la_imax_var(ar, ar->nodes[n].b);
    }
    case LA_IMAX: {
      int32_t x = la_imax_var(ar, ar->nodes[n].a);
      if (x >= 0) return x;
      /* second argument is a VAR after simplification */
      if (ar->nodes[ar->nodes[n].b].kind == LA_VAR)
        return ar->nodes[ar->nodes[n].b].var;
      return la_imax_var(ar, ar->nodes[n].b);
    }
    default:
      return -1;
  }
}

/* subst: replace variable `x` by 0 (mode 0) or by `succ x` (mode 1). */
static int32_t la_subst(la_arena *ar, int32_t n, int32_t x, int mode) {
  if (n < 0) return -1;
  switch (ar->nodes[n].kind) {
    case LA_ZERO:
      return n;
    case LA_VAR:
      if (ar->nodes[n].var != x) return n;
      return mode == 0 ? la_mk_zero(ar) : la_mk_succ(ar, la_mk_var(ar, x));
    case LA_SUCC:
      return la_mk_succ(ar, la_subst(ar, ar->nodes[n].a, x, mode));
    case LA_MAX:
      return la_mk_max(ar, la_subst(ar, ar->nodes[n].a, x, mode),
                       la_subst(ar, ar->nodes[n].b, x, mode));
    case LA_IMAX:
      return la_mk_imax(ar, la_subst(ar, ar->nodes[n].a, x, mode),
                        la_subst(ar, ar->nodes[n].b, x, mode));
    default:
      return -1;
  }
}

/* ------------------------------------------------------------------ */
/* Step 3: canonical form of an `imax`-free level.                     */
/* ------------------------------------------------------------------ */

typedef struct {
  uint32_t k;
  uint8_t  present[LA_MAX_VARS];
  uint32_t off[LA_MAX_VARS];
} la_nf;

static int la_nf_acc(const la_arena *ar, int32_t n, uint32_t shift, la_nf *o) {
  if (n < 0) return 0;
  switch (ar->nodes[n].kind) {
    case LA_ZERO:
      if (shift > o->k) o->k = shift;
      return 1;
    case LA_SUCC:
      return la_nf_acc(ar, ar->nodes[n].a, shift + 1, o);
    case LA_MAX:
      return la_nf_acc(ar, ar->nodes[n].a, shift, o) &&
             la_nf_acc(ar, ar->nodes[n].b, shift, o);
    case LA_VAR: {
      int32_t v = ar->nodes[n].var;
      if (v < 0 || v >= LA_MAX_VARS) return 0;
      o->present[v] = 1;
      if (shift > o->off[v]) o->off[v] = shift;
      return 1;
    }
    default: /* LA_IMAX must not reach here */
      return 0;
  }
}

static int la_to_nf(const la_arena *ar, int32_t n, la_nf *o) {
  memset(o, 0, sizeof(*o));
  if (!la_nf_acc(ar, n, 0, o)) return 0;
  /* the constant is redundant when some present variable's offset covers it */
  for (int i = 0; i < LA_MAX_VARS; i++)
    if (o->present[i] && o->off[i] >= o->k) {
      o->k = 0;
      break;
    }
  return 1;
}

static int la_nf_eq(const la_nf *a, const la_nf *b) {
  if (a->k != b->k) return 0;
  for (int i = 0; i < LA_MAX_VARS; i++) {
    if (a->present[i] != b->present[i]) return 0;
    if (a->present[i] && a->off[i] != b->off[i]) return 0;
  }
  return 1;
}

/* min over rho of the level denoted by `a` (attained at rho = 0). */
static uint32_t la_nf_min(const la_nf *a) {
  uint32_t m = a->k;
  for (int i = 0; i < LA_MAX_VARS; i++)
    if (a->present[i] && a->off[i] > m) m = a->off[i];
  return m;
}

static int la_nf_geq(const la_nf *u, const la_nf *v) {
  if (la_nf_min(u) < v->k) return 0;
  for (int i = 0; i < LA_MAX_VARS; i++) {
    if (!v->present[i]) continue;
    if (!u->present[i]) return 0;
    if (u->off[i] < v->off[i]) return 0;
  }
  return 1;
}

/* ------------------------------------------------------------------ */
/* The recursion.                                                      */
/* ------------------------------------------------------------------ */

static la_result la_go(la_arena *ar, int32_t u, int32_t v, int geq, int depth) {
  if (depth > LA_MAX_SPLITS) return LA_UNKNOWN;
  u = la_simp(ar, u);
  v = la_simp(ar, v);
  if (u < 0 || v < 0) return LA_UNKNOWN;

  int32_t x = la_imax_var(ar, u);
  if (x < 0) x = la_imax_var(ar, v);

  if (x < 0) {
    la_nf nu, nv;
    if (!la_to_nf(ar, u, &nu) || !la_to_nf(ar, v, &nv)) return LA_UNKNOWN;
    if (geq) return la_nf_geq(&nu, &nv) ? LA_TRUE : LA_FALSE;
    return la_nf_eq(&nu, &nv) ? LA_TRUE : LA_FALSE;
  }

  for (int mode = 0; mode < 2; mode++) {
    int32_t u2 = la_subst(ar, u, x, mode);
    int32_t v2 = la_subst(ar, v, x, mode);
    if (u2 < 0 || v2 < 0) return LA_UNKNOWN;
    la_result r = la_go(ar, u2, v2, geq, depth + 1);
    if (r != LA_TRUE) return r; /* FALSE or UNKNOWN both propagate */
  }
  return LA_TRUE;
}

static la_result la_entry(la_arena *ar, int32_t u, int32_t v, int geq) {
  if (ar->nvars > LA_MAX_VARS) return LA_UNKNOWN;
  la_result r = la_go(ar, u, v, geq, 0);
  if (ar->overflow) return LA_UNKNOWN;
  return r;
}

la_result la_equiv(la_arena *ar, int32_t u, int32_t v) {
  return la_entry(ar, u, v, 0);
}

la_result la_geq(la_arena *ar, int32_t u, int32_t v) {
  return la_entry(ar, u, v, 1);
}

/* ------------------------------------------------------------------ */
/* The oracle and the printer.                                         */
/* ------------------------------------------------------------------ */

uint32_t la_eval(const la_arena *ar, int32_t n, const uint32_t *rho) {
  if (n < 0) return 0;
  switch (ar->nodes[n].kind) {
    case LA_ZERO:
      return 0;
    case LA_SUCC:
      return la_eval(ar, ar->nodes[n].a, rho) + 1;
    case LA_MAX: {
      uint32_t a = la_eval(ar, ar->nodes[n].a, rho);
      uint32_t b = la_eval(ar, ar->nodes[n].b, rho);
      return a > b ? a : b;
    }
    case LA_IMAX: {
      uint32_t b = la_eval(ar, ar->nodes[n].b, rho);
      if (b == 0) return 0;
      uint32_t a = la_eval(ar, ar->nodes[n].a, rho);
      return a > b ? a : b;
    }
    case LA_VAR:
      return rho[ar->nodes[n].var];
    default:
      return 0;
  }
}

typedef struct {
  char   *buf;
  int32_t sz;
  int32_t at;
} la_pr;

static void la_emit(la_pr *p, const char *s) {
  while (*s && p->at + 1 < p->sz) p->buf[p->at++] = *s++;
  p->buf[p->at] = 0;
}

static void la_pr_go(const la_arena *ar, int32_t n, la_pr *p,
                     const char *const *varnames) {
  if (n < 0) {
    la_emit(p, "<bad>");
    return;
  }
  switch (ar->nodes[n].kind) {
    case LA_ZERO:
      la_emit(p, "0");
      break;
    case LA_SUCC:
      la_emit(p, "(succ ");
      la_pr_go(ar, ar->nodes[n].a, p, varnames);
      la_emit(p, ")");
      break;
    case LA_MAX:
    case LA_IMAX:
      la_emit(p, ar->nodes[n].kind == LA_MAX ? "(max " : "(imax ");
      la_pr_go(ar, ar->nodes[n].a, p, varnames);
      la_emit(p, " ");
      la_pr_go(ar, ar->nodes[n].b, p, varnames);
      la_emit(p, ")");
      break;
    case LA_VAR: {
      if (varnames && varnames[ar->nodes[n].var])
        la_emit(p, varnames[ar->nodes[n].var]);
      else {
        char t[16];
        snprintf(t, sizeof(t), "?%d", ar->nodes[n].var);
        la_emit(p, t);
      }
      break;
    }
    default:
      la_emit(p, "<?>");
      break;
  }
}

void la_print(const la_arena *ar, int32_t n, char *buf, int32_t bufsz,
              const char *const *varnames) {
  la_pr p = {buf, bufsz, 0};
  if (bufsz > 0) buf[0] = 0;
  la_pr_go(ar, n, &p, varnames);
}
