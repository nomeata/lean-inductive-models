/-
The public nested-iota statement must use the exported recursor minor rather
than reconstructing its field telescope from the constructor.  Lean retains
the default wrapper on the constructor argument but exposes its reduced domain
in the recursor minor, exactly as in `Lean.Compiler.LCNF.Alt`.
-/
prelude

--#export optParam Eq List NestedDefault

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (value : α) : Eq value value

inductive List (α : Type u) : Type u where
  | nil : List α
  | cons : α → List α → List α

inductive NestedDefault (α : Type u) where
  | node (value : α) (children : List (NestedDefault α))
      (canonical := Eq.refl value) : NestedDefault α
