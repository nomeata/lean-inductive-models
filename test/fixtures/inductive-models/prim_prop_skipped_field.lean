/- **A proposition's projectable field behind a field the kernel skips.**

   Lean's `infer_proj` walks the constructor telescope once per projection and
   substitutes an earlier field only where the *rest of the telescope still
   names it*:

   ```cpp
   for (unsigned i = 0; i < idx; i++) {
     if (has_loose_bvars(binding_body(r))) {
       if (is_prop_type && !is_prop(binding_domain(r))) throw ...;
       r = instantiate(binding_body(r), mk_proj(I_name, i, proj_expr(e)));
     } else {
       r = binding_body(r);   // no projection of field i is formed at all
     }
   }
   ```

   So a proposition-valued owner may carry a **data** field and still have a
   projectable proof field after it, provided nothing later names the data
   field. The tool's own eligibility walk
   ([`InductiveModels.eligibleProjectionFieldsM`], and its two syntax mirrors
   in `Check/Index.lean` and `Format/Exact.lean`) is exactly that loop, so it
   reports such an owner's field list with a **hole** in it: field 0 absent,
   field 1 present.

   That hole is what this file is about. `addProjectionModels` used to read
   the projected field's type by substituting *every* earlier field's
   intrinsic projection unconditionally, and so demanded a projection for a
   field the kernel never projects. On the two owners below it raised

       internal error: PropSkip's field 1 precedes intrinsic field 0

   and stopped the run at exit 3 — on a declaration the kernel accepts. The
   walk now drops a binder exactly where the kernel drops it, and the lookup
   is asked only where the dependence is real. There it is a genuine
   invariant: a field the remaining telescope names is one the eligibility
   walk required to be a proposition, hence eligible itself and already
   emitted, because projections are emitted in field order.

   The four owners are the grid of that walk on a proposition:

   * `PropSkip` — the reported shape: a `Type` parameter, one data field, and
     a **recursive** proof field that does not name it. Field 1 projects,
     field 0 does not exist as a projection.
   * `PropSkipFlat` — the same hole with no recursion and no owner-typed
     field, so the row cannot be read as being about recursion. Neither the
     recursion nor the parameter is what the walk reacts to; a non-proposition
     field followed by a proof field that ignores it is.
   * `PropDep` — the control on the other side of the `has_loose_bvars` test:
     the proof field *does* name the data field, so the kernel refuses that
     projection and so does the tool. The owner still models, with no
     projection at all; a fix that reached the field by substituting a
     projection of the data field would show up here as a fifth and sixth
     declaration.
   * `PropChain` — the control for the branch that still substitutes: both
     fields are proofs, field 1 names field 0, and field 1's projected
     codomain is stated at field 0's *projection*. Dropping the substitution
     everywhere rather than only where the binder is unused would break this
     one.

   `N` is the ordinary control: a run that declined everything could not pass
   this row. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive N : Type where
  | z : N
  | s : N → N

--#export Eq N PropSkip PropSkipFlat PropDep PropChain

inductive PropSkip (a : Type) : Prop where
  | mk : a → PropSkip a → PropSkip a

inductive PropSkipFlat (a : Type) : Prop where
  | mk : a → Eq N.z N.z → PropSkipFlat a

inductive PropDep (a : Type) : Prop where
  | mk : (x : a) → Eq x x → PropDep a

inductive PropChain (p : Prop) (q : p → Prop) : Prop where
  | mk : (hp : p) → q hp → PropChain p q
