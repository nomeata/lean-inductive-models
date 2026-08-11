/- **At `σ` a `Sort u` inductive can land in `Prop`, and the kernel's *derived*
   properties move with it.**

   `PU.{0}` is a proposition with one argument-free constructor, which the kernel
   marks **K-like**; `PU.{1}` is a `Type` and is not. So the export's own
   `k : false` is a lie about the copy at `0`, and substituting the recursor
   rather than letting the kernel mint it produces an invalid derived recursor.
   `Ex.{u}` moves the other way:
   it is small-eliminating polymorphically, and its copy at `0` is
   large-eliminating, so a reference at no levels becomes ill-formed.

   Both directions in one file, and the fixture is degenerate without both. -/
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

-- The same escape hatch Lean's own `Prelude` uses for `PUnit`: a `Sort u`
-- inductive is rejected by default *because* it may land in `Prop`.
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PU : Sort u where
  | unit : PU

inductive Ex (α : Sort u) (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Ex α p

--#export puProp puType exAt0 exAt1

def puProp : PU.{0} := PU.unit
def puType : PU.{1} := PU.unit
def exAt0 (p : Eq N.z N.z → Prop) (h : Ex.{0} (Eq N.z N.z) p) : Eq N.z N.z :=
  Ex.rec.{0} (motive := fun _ => Eq N.z N.z) (fun _ _ => Eq.refl N.z) h

def exAt1 (p : N → Prop) (h : Ex.{1} N p) : Eq N.z N.z :=
  Ex.rec.{1} (motive := fun _ => Eq N.z N.z) (fun _ _ => Eq.refl N.z) h
