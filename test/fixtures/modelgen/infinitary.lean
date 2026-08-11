/- **A constructor field recursive under a binder.** Lean supports infinitary
   constructors, and there are three places one can sit relative to the
   nesting. All three are here, because they are handled by different code:

   * `FTree.branch : (N → FTree) → FTree` — the **root's** own field, under a
     binder. The block types it `N → B₀`, and `B₀.rec`'s minor for it carries
     `(n : N) → motive₀ (f n)`.
   * `Fn.mk : (N → α) → Fn α`, reached as `FTree.node : Fn FTree → FTree` — the
     **mimic's** field. `B₁.mk : (N → B₀) → B₁`, and `B₁.rec`'s rule gives that
     an induction hypothesis too.
   * `HTree.node : (N → List HTree) → HTree` — a field at a **mimic** under a
     binder. Lean accepts it; `HTree.rec_1`'s minor for `node` binds
     `a : N → List HTree` with `(a_1 : N) → motive_2 (a a_1)`.

   A field at a mimic under a binder is the one shape here whose proofs need a
   `funext`, and **this file declares none** — so `modelgen` derives one from
   `Quot.sound` and splices it in beside the model. It has
   **three** witnesses rather than one, at three different proofs, and all three
   are models. Each is a `funext` and Lean accepts all three:

   * `HTree.node : (N → List HTree) → HTree` — the **root's** field. The
     recursor's minor has to transport along `(fun n => pack₀ (unpack₀ (f n)))
     = f`, and so does every ι rule of `HTree.rec`.
   * `RTree.mk : Rose RTree → RTree`, where `Rose.node : (N → Rose α) → Rose α`
     — the container's **own recursive** field, under a binder. `pack` and
     `unpack` need nothing (the induction hypothesis is already the function
     they want); the two **round trips** need funext, because `unpack₀ (pack₀
     (Rose.node f))` reduces to `Rose.node (fun n => unpack₀ (pack₀ (f n)))`.
   * `OTree.mk : Outer OTree → OTree`, where `Outer.mk : (N → Inner α) → Outer
     α` — a container's field at **another** mimic, under a binder. `Outer` is
     not recursive at all, so there is no induction hypothesis to lean on and
     the round trips transport along `funext (fun n => unpackPack₁ (f n))`.

   The three are also what says the splice happens **once**: `HTree` pays for
   the quotient, `Quot.sound` and its own `funext`, and `RTree` and `OTree` find
   the quotient already installed and pay for a `funext` alone — 18, 14 and 20
   declarations against `funext_binder.lean`'s 15, 13 and 19 for the same three
   shapes with a `funext` in the file.

   Three, because the first cannot reach the other two: `HTree`'s binder is at
   the root and never enters `retractValue` or `sectionValue`, and `RTree`'s
   sits at a position that *has* an induction hypothesis where `OTree`'s does
   not.

   `Fn3.mk : (N → α) → List α → Fn3 α`, reached as `ZTree.node : Fn3 ZTree →
   ZTree`, is the one that actually *pins* the hypothesis vector. A minor's
   vector has one entry per field that has a hypothesis, in field order, and an
   infinitary field has one while sitting at no member; `B₁.mk`'s second field
   is at the deeper mimic `B₂`, so a treatment that indexed the vector by the
   fields *at* a member would hand it `(N → B₀)`'s hypothesis and the kernel
   would refuse `unpack_0`. Measured: with that indexing `ZTree` declines.

   `GTree.mix : (N → GTree) → List GTree → GTree → GTree` is here because the
   first two on their own cannot distinguish an ordering. A minor's hypothesis
   vector has one entry per field that *has* a hypothesis, in field order, and
   an infinitary field has one while sitting at no member; a treatment that
   indexed the vector by the fields at a member would hand `List GTree`'s
   hypothesis to `(N → GTree)`. Three ih-bearing fields, and the packed one in
   the middle, is what makes that visible. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

--#export Eq N List Fn Fn3 Rose Inner Outer FTree GTree ZTree HTree RTree OTree

inductive Fn (α : Type) : Type where
  | mk : (N → α) → Fn α
  | pure : α → Fn α

inductive Fn3 (α : Type) : Type where
  | mk : (N → α) → List α → Fn3 α

inductive Rose (α : Type) : Type where
  | leaf : α → Rose α
  | node : (N → Rose α) → Rose α

inductive Inner (α : Type) : Type where
  | mk : α → Inner α

inductive Outer (α : Type) : Type where
  | mk : (N → Inner α) → Outer α

inductive FTree : Type where
  | leaf : FTree
  | branch : (N → FTree) → FTree
  | node : Fn FTree → FTree

inductive HTree : Type where
  | leaf : HTree
  | node : (N → List HTree) → HTree

inductive RTree : Type where
  | mk : Rose RTree → RTree

inductive OTree : Type where
  | mk : Outer OTree → OTree

inductive GTree : Type where
  | leaf : GTree
  | mix : (N → GTree) → List GTree → GTree → GTree

inductive ZTree : Type where
  | leaf : ZTree
  | node : Fn3 ZTree → ZTree
