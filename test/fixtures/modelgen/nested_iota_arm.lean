/-
# The ι dispatch arm, at the smallest input that separates its two answers

`nested_iota.lean` is the specification — fourteen rules over three nested
declarations at two containers — and it is four minutes of conversions. This
file is the *arm*: one nested declaration, its two recursors, and all four of
its rules, which is the smallest input on which the arm both **fires** and
**declines**, and it runs in a fraction of the time.

The split it pins is not a split in the fixture. All four theorems below are
`rfl` and Lean's own kernel checked all four; what differs is the **model's**
proof of the corresponding rule:

| rule | the model's proof | mini |
| --- | --- | --- |
| `treeIotaLeaf`  (`Tree.rec` on `Tree.leaf`)    | `Eq.refl`  | certifies |
| `treeIota1Nil`  (`Tree.rec_1` on `List.nil`)   | `Eq.refl`  | certifies |
| `treeIotaNode`  (`Tree.rec` on `Tree.node`)    | transport  | declines  |
| `treeIota1Cons` (`Tree.rec_1` on `List.cons`)  | transport  | declines  |

`Tree.node` and `List.cons` each carry a field at the specialised copy of
`List`, so `nested_ev`'s rule has to move it along `unpackPack` — and a
transport that must be *reduced* rather than compared is #90(b). The two rules
that transport are therefore **not seeded** by `nested_splice` and have no
`model_iota` entry, and the arm has to say so by name rather than borrow
`iota_dep`'s reason or fall through to it. That decline is half of what this
file measures and it is the half a fixture with only the easy rules would miss.

`Tree.rec_1` is the reason the whole arc exists: a recursor for one declaration
that ι-reduces on **another declaration's** constructors. Both of its rules are
here, one on each side of the split.

Everything is stated at **variable** motives, minors and majors: a closed major
reduces one constructor at a time whatever the rule says. The motives land in
`Type` and not in `Prop` for `nested_iota.lean`'s reason — proof irrelevance
would close every equation below without reducing anything — and `N` rather
than `Nat` is the payload for `infinitary_branching.lean`'s.
-/
prelude

--#export Eq N List Tree
--#export treeIotaLeaf treeIotaNode treeIota1Nil treeIota1Cons
--#export treeSize

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The payload, so that a motive can land in `Type` without `Nat`. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- The container. -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

/-- Depth 1, one container — the smallest nested declaration there is. -/
inductive Tree : Type where
  | leaf : Tree
  | node : List Tree → Tree

/-- A use of the nested recursor at a closed motive, so the file measures the
    evidence axis and not only the acceptance axis. -/
noncomputable def treeSize : Tree → N :=
  @Tree.rec (fun _ => N) (fun _ => N)
    N.z
    (fun _ ih => N.s ih)
    N.z
    (fun _ _ ih1 ih2 => N.s (N.s ih1))

section Tree

variable (m1 : Tree → Type) (m2 : List Tree → Type)
variable (lf : m1 Tree.leaf)
variable (nd : ∀ a : List Tree, m2 a → m1 (Tree.node a))
variable (nl : m2 (@List.nil Tree))
variable (cs : ∀ (a : Tree) (b : List Tree), m1 a → m2 b → m2 (@List.cons Tree a b))

/-- The model proves this one by `Eq.refl`: `Tree.leaf` has no field, so the
    pack/unpack fold has nothing to move. -/
theorem treeIotaLeaf : Eq (@Tree.rec m1 m2 lf nd nl cs Tree.leaf) lf :=
  Eq.refl _

/-- The model transports this one: `Tree.node`'s field is at the mimic. -/
theorem treeIotaNode (a : List Tree) :
    Eq (@Tree.rec m1 m2 lf nd nl cs (Tree.node a))
       (nd a (@Tree.rec_1 m1 m2 lf nd nl cs a)) :=
  Eq.refl _

/-- `Eq.refl` in the model, on the **other** recursor: `List.nil` is a rule of
    `Tree.rec_1`, which eliminates `List Tree`. -/
theorem treeIota1Nil : Eq (@Tree.rec_1 m1 m2 lf nd nl cs (@List.nil Tree)) nl :=
  Eq.refl _

/-- The second transport, and the cross-reference: `Tree.rec_1`'s rule for
    `List.cons` calls **both** recursors. -/
theorem treeIota1Cons (a : Tree) (b : List Tree) :
    Eq (@Tree.rec_1 m1 m2 lf nd nl cs (@List.cons Tree a b))
       (cs a b (@Tree.rec m1 m2 lf nd nl cs a) (@Tree.rec_1 m1 m2 lf nd nl cs b)) :=
  Eq.refl _

end Tree
