/- **A name the renaming cannot reach by prefix surgery.**

   `monomorph`'s naming scheme used to rename a declaration by replacing an
   *owner* prefix — a constructor's inductive, a recursor's block member — with
   that owner plus the marker. That is the identity whenever the owner is **not**
   a prefix of the name, and then every copy of the block is named the same
   thing. Mathlib is full of the shape (`MONOMORPH.md` §9.2: 142 of 9299
   constructors, and `AddMonCat.Hom.mk` is one), and no corpus file was.

   `Off.{u}` is a **public** inductive with a **private** constructor, so the
   constructor is `_private.MonoOffname.0.Off.mk` and `Off` is nowhere in it.
   It is used at **three** distinct universes: two copies would collide under
   the old scheme just as three do, but three also pin that the marker carries
   the instantiation rather than a serial number.

   The recursor is the other half. Lean and `nanoda` both *derive* `Off.rec`
   from `Off`, so the copy's recursor has to be the copy's name plus `rec` —
   which is what a prefix renaming gives for free and a suffix renaming does
   not. `regen = 0` here says the kernel minted exactly what was emitted. -/
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
