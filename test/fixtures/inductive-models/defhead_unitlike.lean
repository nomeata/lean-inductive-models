/- **Unit-like owners whose sort is behind a definition.**

   `T._model.unitlike` states `∀ p⃗ (x y : T._model p⃗), x = y`, and the
   equality lives in the carrier's sort. When the former is written
   `inductive U : MyProp` with `def MyProp := Prop`, that sort is `Prop` only
   after unfolding `MyProp`, so the witness is an `Eq.{0}`; the structural
   checker reads the former's result with the export's own head normalisation
   (as its η check already did) rather than requiring a literal `Sort`. It used
   to find no `Sort` there, have no proposition to compare against, and report
   the generated theorem as not literally modelling the owner — on a
   declaration the kernel accepts. con-leche's `ind_defhead_k` is `U`.

   * `U` — a proposition behind a definition: `Eq.{0}`.
   * `UT` — a `Type` behind a definition: `Eq.{1}`.
   * `UP` — a parameterised proposition, so the parameter binders are opened
     from the written telescope and only the result is normalised.
   The normalisation is the checker index's, which sees the source prefix the
   sort is defined in; an island on its own does not contain `MyProp`.
-/

def MyProp : Type := Prop
def MyType : Type 1 := Type
def PropF : Type := Prop

--#export U UT UP

inductive U : MyProp where
  | u

inductive UT : MyType where
  | u

inductive UP (α : Type) : PropF where
  | u
