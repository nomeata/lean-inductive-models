prelude

/-!
Transparent aliases of a recursive owner are ordinary recursive occurrences,
not nested occurrences.  Lean's positivity and recursor generation unfold
`At` and `As`, while the exported constructor and recursor types retain those
names.  Model generation may therefore unfold them for routing and index
recovery only; its public declarations must preserve the literal spelling.

`AliasI` exercises the indexed Type erasure route, `AliasP` the large-
eliminating one-constructor Prop graph route, and `AliasC` the maybe-zero
Church route.  Keeping the three shapes together distinguishes the shared
owner-recognition seam from each representation's internal encoding.
-/

set_option bootstrap.inductiveCheckResultingUniverse false
set_option genSizeOf false

universe u v

--#export Eq N At As AliasI AliasP AliasC

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

def At {ι : Sort u} (F : ι → Sort v) (i : ι) : Sort v := F i

def As (α : Sort u) : Sort u := α

inductive AliasI : N → Type where
  | base : AliasI N.z
  | step (n : N) : At AliasI n → AliasI (N.s n)

inductive AliasP (n : N) : Prop where
  | intro : As (AliasP n) → AliasP n

inductive AliasC : Sort u where
  | leaf : AliasC
  | step : As AliasC → AliasC
