/- **Arm G's positive shapes** (`src/Modelgen/Simple.lean`'s
   [`Modelgen.graphArm`]): the recursive subsingleton, modelled by the **graph**
   of its own recursion. This is the arm that took `Acc` out of the basis, and
   these are the exported shapes for the choice-based and `PSigma'`-based routes.

   Two lines of the recipe are shape-sensitive — the n-ary congruence in
   `Graph.unique` and the `funext` chain, which runs per **binder** of a
   recursive field — so the occupants are chosen to make both fail if they are
   wrong:

   * `G1` — the **degenerate** shape: no parameters, no indices, one recursive
     field with **no binders**. The recursive "argument function" is not a
     function, so the induction hypothesis hands `f1 = f2` over directly and
     one `congrArg` closes `Graph.unique`. **Its ι costs no `funext`** and
     therefore no `Quot.sound`, which is the measurement that says the axiom
     cost is per shape and not per arm.
   * `Ac` — **`Acc`'s own shape**, universe-polymorphic in the carrier of the
     relation: one data field that *is* the index, one recursive field under
     **two** binders. This is the declaration whose presence in the basis this
     arm removed.
   * `G2` — **two** recursive fields, at **different** domains (`r` and `s`).
     The shape on which a single `congrArg (step x h1 h2)` is insufficient: the
     congruence has to be binary, composed through the intermediate term. The
     domains differ on purpose — two *identical* recursive fields could not
     catch a field-order bug, because swapping them would still typecheck.
   * `G3` — a non-recursive proof field on **both sides** of the recursive one,
     three fields in all, pairwise distinguishable (`q`, the recursive field,
     `p x`), so any permutation is a type error. With fields only before, or
     only after, the recursion an ordering bug is invisible.
   * `G4` — the `accφ` shape: a proof field the **relation itself depends on**
     (`R : (x : ι) → A x → ι → Prop`), so the recursive field's own domain
     mentions an earlier field. Inversion recovers it by proof irrelevance,
     which is the clause that generalises.

   * `G5` — **three** indices, and the constructor's data fields map onto them
     by a **permutation** (`mk a b c h : G5 r c a b`). Three atoms, not two:
     with one index the field↦index map is the identity and with two a
     transposition is invisible in half the shapes, so three is the first arity
     at which a wrong map has to show. The recursive field lands at a *third*
     index vector again, so nothing here is the identity by accident.

   Four of the six have indices and two do not; four have a recursive field
   with binders and one has none; one, two, three and four fields are all
   present.

   **The file declares `Eq` and nothing else**, so one run splices everything
   else the arm needs and the report names it: `PSigma'` (the value is paired
   with its graph proof), `Nonempty` and `Classical.choice` (the extraction),
   and — for the first shape with a binder — the quotient, `Quot.sound` and a
   derived `funext`. `prim_graph_pre.lean` is the same arm on an input that
   declares those itself, and splices nothing.

   `N` beside them is an ordinary `Type`-route model and the control that says
   the arm is not swallowing everything. `BadC` forces the transport case: its
   index is a **constant** rather than one of the constructor's data fields,
   so graph inversion must move the step value from `N.z` to its arbitrary
   caller index. The `.below` declarations add proof-valued non-pivots, and
   together pin the dependent packed equality used by the same transport. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive N : Type where
  | z : N
  | s : N → N

inductive G1 : Prop where
  | mk : G1 → G1

inductive Ac {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Ac r y) : Ac r x

inductive G2 (r s : N → N → Prop) : N → Prop where
  | mk (x : N) (h1 : (y : N) → r y x → G2 r s y)
       (h2 : (y : N) → s y x → G2 r s y) : G2 r s x

inductive G3 (q : Prop) (p : N → Prop) (r : N → N → Prop) : N → Prop where
  | mk (x : N) (hq : q) (h : (y : N) → r y x → G3 q p r y) (hp : p x) : G3 q p r x

inductive G4 {ι : Sort u} (A : ι → Prop) (R : (x : ι) → A x → ι → Prop) : ι → Prop where
  | mk (x : ι) (a : A x) (h : (y : ι) → R x a y → G4 A R y) : G4 A R x

inductive G5 (r : N → N → N → Prop) : N → N → N → Prop where
  | mk (a : N) (b : N) (c : N) (h : (y : N) → r a y c → G5 r y b a) : G5 r c a b

inductive BadC : N → Prop where
  | mk : BadC N.z → BadC N.z
