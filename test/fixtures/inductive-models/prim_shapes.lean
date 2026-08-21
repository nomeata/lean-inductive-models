/- **The simple-model construction's positive shapes**
   (`src/InductiveModels/Simple.lean`), one per route variant:

   * `Tri` — a **three**-element enumeration, because two atoms cannot
     distinguish an ordering: three nullary constructors pin tag order and
     the `D 1` pads (`Σ'(_ : ⊤), ⊤`) all three chains are.
   * `Boxed` — a structure with a **dependent `Prop` field**: the chain
     `Σ'(val : α), Eq val val` reaches `Sort (u+1)` on its own, no pad.
   * `Opt` — a parameter and a **nullary constructor at `Type u`**, whose
     chain is the pad alone, at the successor form `D (u+1) = (α : Sort u) →
     D 1`.
   * `Big` — a **deliberately-raised carrier** (`Type 1` over a `Type 0`
     field), the one shape whose pad is `D w` at `w` above both `1` and the
     fields.
   * `Dec` — a `Type`-valued sum whose fields are **propositions**, so both
     chains need the `D 1` pad tier (`max 1 0 ≠ 0`).
   * `Sub` — a `Sort (max 1 u)` carrier with a `Sort u` field and a `Prop`
     field: the `PSigma'` chain lands on the declared level exactly.
   * `Emp` — **no constructors**: the fibre is empty at every tag and the
     recursor is Church-`⊥`'s `Sort w` eliminator under two destructions.
   * `Tor` — a `Prop` with three constructors: small elimination, the Church
     fold at a `Prop` motive.
   * `IdxP` — an **indexed** `Prop` with two constructors landing at
     *different* indices: small elimination, so the carrier is the Church
     encoding with `C` quantified over the index telescope. Non-recursive —
     it isolates indices from recursion.
   * `Le3` — **indexed and recursive**, three constructors with pairwise
     distinguishable telescopes (nullary; one recursive field; a recursive
     field *followed* by a non-recursive one) landing at three different
     indices. This is the strong-induction
     fold: three atoms, because a two-constructor family cannot catch a
     minor-order bug, and distinguishable telescopes, because ι is `rfl` by
     proof irrelevance here and so cannot catch one either — what catches a
     permutation is the minor premise failing to typecheck.
   * `Conj` and `Conj3` — a `Prop` structure with **dependent**
     propositional fields, two of them and three: large elimination by
     sequential extraction, a later field's type instantiated at the earlier
     extractions and closed by definitional proof irrelevance. Three, not
     two, because with two fields the *first* extraction is the only
     predecessor, so a version that instantiates every field's type at
     extraction 0 rather than at its own predecessors is green at `Conj` and
     red only at `Conj3`.
   * `PU` — a **variable-sort singleton** (`PUnit`'s shape): the carrier is
     the derived lift of `⊤` at exactly `Sort u`, the recursor a transport along the
     lift's eta.
   * `PE` — a **variable-sort empty carrier** (`PEmpty`'s shape): the
     carrier is the derived lift of `⊥`, and the recursor — zero minor premises — is
     Church-`⊥`'s `Sort w` eliminator after the lift is projected away.
     This is the shape the old basis could not reach at all.
   * `PM` — a variable-sort carrier with **two** constructors: small
     elimination, so the lift of the Church encoding serves both.
   * `PT` — a variable-sort carrier with **three** constructors carrying
     **distinguishable** field telescopes. Three atoms, not two: with three
     nullary constructors a minor-order bug is invisible (the motive is
     `Prop`-valued and proof irrelevance closes it), so the fields are what
     make a permutation a type error.
   * `PF` — a variable-sort carrier whose constructor has a **field**.
   * `PI` — a variable-sort carrier whose field is at the **carrier's own**
     sort (`is_geq(u,u)`, the kernel's admission at its tightest): small
     elimination, and the model collapses the payload, which the contract
     permits because a `Prop`-valued motive cannot discriminate.
   * `UL` — `PULift`'s shape: a carrier raised by a level (`r`) no field
     reaches, whose pad level is not `dsingOk` — the derived `⊤` pad,
     discharged by transport in the destructor.
   * `Lst` — the linear-recursion tower at its simplest: one base
     constructor with no fields, one step constructor with the recursive
     field **last**, level-polymorphic.
   * `MNm` — `Lean.Name`'s shape: no parameters, **three** constructors, the
     recursive field **first**, two step tags with different payloads.
   * `Weave` — the shape that pins the base/step split and the tag map,
     which neither of the other two can: four constructors in the
     **interleaved** order base, step, base, step, so the export index →
     (tower, tag) map is not "all bases first"; a step constructor with
     fields **both before and after** the recursive one; a `Prop` field in a
     base chain, so the pad is doing real work. `s0` and `s1` are given the
     *same* telescope deliberately — that is what lets a non-injective tag
     collision typecheck and therefore be caught only by an ι rule.
   * `IdxS` — an indexed **subsingleton** at its simplest: one constructor,
     no fields, one index. Large elimination, so the carrier is the packed
     index equation and not a Church fold.
   * `TagS` — the same with a genuine `Prop` field, which rides as an extra
     Church-conjoined component and comes back out by small elimination.
   * `TagS2`, `TagS3` and `TagS4` — **two and three** `Prop` fields,
     dependent and non-dependent. These exist because `TagS`'s single field
     cannot catch a field-order bug: a mutation reversing the extracted
     fields is a no-op on one field, and was measured green until these
     existed. `TagS4`'s three fields are what pin the order rather than a
     transposition of it, and its chain (`h : q`, `k : t h`, `w h k`) makes
     the sequential instantiation run **twice**, so a version that reads a
     later field's type off the raw telescope instead of off the earlier
     extractions is red here and at `TagS2`.
   * `Hq` — `HEq`'s shape widened to **three** indices, the second dependent
     on the first (`{β : Sort u}` then `b : β`). Three atoms: with one index
     the packing is the identity and with two a transposition is invisible in
     half the shapes, so three is the first arity at which a pack/unpack
     ordering bug has to show.
   * `TrL` — `Trans`'s shape: a Π-typed field at an **imax** level, stored
     **recursively boxed** (atomic leaves wrapped as `Σ'(_ : S), D 1`) so the
     level collapses to the carrier's never-zero `max`; the recursor unboxes
     by projection and needs no transport at all.

   * `Sv` — a carrier whose **index telescope is hidden behind a
     definition**: `Sv (x : Tri) : SvFam x` where `SvFam x := Tri → Tri →
     Prop`. Lean stores an inductive's type as *declared*, so a syntactic peel
     of `Sv`'s type finds `SvFam x` — not a `Sort`, and no indices at all —
     while `Sv.rec` carries two. This is `CategoryTheory.Presieve.ofArrows`'s
     shape and that of seventeen more like it in Mathlib. **Two** hidden
     indices rather than one, because with one a model that guessed a fixed
     count would still pass; two is where the count has to come from the
     unfolding. From there it is an ordinary indexed subsingleton and the recovery arm
     models it. `prim_declines.lean`'s `SvIx` is the same hidden telescope
     with *field-dependent* indices: after the same unfolding, the recovery arm's
     pivot/non-pivot transport models it. The pair verifies that telescope
     unfolding composes with the dependent index analysis.

   The file declares `Eq` and nothing else of the basis, so one run splices
   `Nat`, `PSigma'`, and `PUnit` and the report names them. Nothing here
   splices the quotient, `Quot.sound` or a `funext`: the lift's eta replaced
   the one construction that needed them. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe r s u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive Tri : Type where
  | a : Tri
  | b : Tri
  | c : Tri

inductive Boxed (α : Type u) : Type u where
  | mk : (val : α) → Eq val val → Boxed α

inductive Opt (α : Type u) : Type u where
  | none : Opt α
  | some : α → Opt α

inductive Big : Type 1 where
  | mk : (Prop → Prop) → Big

inductive Dec (p : Prop) : Type where
  | isF : ((h : p) → Eq p p) → Dec p
  | isT : p → Dec p

inductive Sub (α : Sort u) (p : α → Prop) : Sort (max 1 u) where
  | mk : (val : α) → p val → Sub α p

inductive Emp : Type where

inductive Tor (a b c : Prop) : Prop where
  | l : a → Tor a b c
  | m : b → Tor a b c
  | r : c → Tor a b c

inductive Conj (a : Prop) (b : a → Prop) : Prop where
  | mk : (ha : a) → b ha → Conj a b

inductive Conj3 (a : Prop) (b : a → Prop) (c : (ha : a) → b ha → Prop) :
    Prop where
  | mk : (ha : a) → (hb : b ha) → c ha hb → Conj3 a b c

inductive IdxP : Tri → Prop where
  | at_a : IdxP Tri.a
  | at_b : IdxP Tri.b

inductive Le3 (q : Prop) : Tri → Prop where
  | base : Le3 q Tri.a
  | up : Le3 q Tri.a → Le3 q Tri.b
  | tagged : Le3 q Tri.b → q → Le3 q Tri.c

inductive PU : Sort u where
  | mk : PU

inductive PE : Sort u where

inductive PM : Sort u where
  | a : PM
  | b : PM

inductive PT (p q : Prop) : Sort u where
  | x : p → PT p q
  | y : q → PT p q
  | z : p → q → PT p q

inductive PF : Sort u where
  | mk : ((C : Prop) → C → C) → PF

inductive PI (α : Sort u) : Sort u where
  | mk : α → PI α

inductive UL (α : Sort s) : Sort (max s r 1) where
  | up : α → UL α

inductive TrL (α : Sort u) (r : α → α → Sort v) : Sort (max 1 u v) where
  | mk : ((a b : α) → r a b) → TrL α r

inductive Lst (α : Type u) : Type u where
  | nil : Lst α
  | cons : α → Lst α → Lst α

inductive MNm : Type where
  | anon : MNm
  | str : MNm → Tri → MNm
  | num : MNm → Opt Tri → MNm

inductive IdxS : Tri → Prop where
  | mk : IdxS Tri.a

inductive TagS (q : Prop) : Tri → Prop where
  | mk : q → TagS q Tri.a

inductive TagS2 (q : Prop) (t : q → Prop) : Tri → Prop where
  | mk : (h : q) → t h → TagS2 q t Tri.a

inductive TagS3 (q s : Prop) : Tri → Prop where
  | mk : q → s → TagS3 q s Tri.a

inductive TagS4 (q : Prop) (t : q → Prop) (w : (h : q) → t h → Prop) :
    Tri → Prop where
  | mk : (h : q) → (k : t h) → w h k → TagS4 q t w Tri.a

inductive Hq : {α : Sort u} → α → {β : Sort u} → β → Tri → Prop where
  | refl (a : α) : Hq a a Tri.a

inductive Weave (α : Type u) (p : Prop) : Type u where
  | b0 : Weave α p
  | s0 : α → Weave α p → p → Weave α p
  | b1 : α → p → Weave α p
  | s1 : α → Weave α p → p → Weave α p

def SvFam (x : Tri) : Type := Tri → Tri → Prop

inductive Sv (x : Tri) : SvFam x where
  | mk : Sv x Tri.a Tri.b
