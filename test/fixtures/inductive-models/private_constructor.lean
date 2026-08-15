/- A public inductive with a private constructor. The constructor's exact raw
   export name is not below the public owner prefix, so model naming must use
   the declaration metadata rather than namespace surgery. Multiple universe
   use sites ensure the fixture remains genuinely polymorphic. -/
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

structure Off (α : Sort u) : Sort (max 1 u) where
  private mk ::
  val : α

--#export atProp atType atType1

def atProp (w : Off.{0} (Eq N.z N.z)) : Off.{0} (Eq N.z N.z) := w
def atType (w : Off.{1} N) : Off.{1} N := w
def atType1 (w : Off.{2} Type) : Off.{2} Type := w
