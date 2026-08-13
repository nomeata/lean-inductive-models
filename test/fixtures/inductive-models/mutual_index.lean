/- **A plain mutual block whose members carry indices**, which is where the
   encoding stops being an enumeration.

   The tag's constructors carry **that member's own index telescope** as their
   fields, so the members are not required to agree on anything — the way the
   kernel *does* require them to agree on their parameters and their sort. Each
   block below removes one way of being degenerate about that.

   * `T0`/`T1`/`T2 : N → Type` — one index each, the same type, the same
     length. The shape, and the one a treatment that promoted the shared
     telescope out of the tag would also pass.
   * `MA : N → Type`, `MB : Type`, `MC : N → Type` — **telescopes of different
     lengths in one block**. `MB` contributes a nullary tag constructor beside
     two unary ones, and `MB.rec` has no index where its siblings have one, so
     a single index arity read off the first member is wrong here.
   * `DA : N → Type`, `DB : Bit → Type` — same *length*, different index
     **type**. `N` and `Bit` are both at `Sort 1`, so this axis is held apart
     from the sort of the index below: only the type differs.
   * `SA`/`SB`/`SC (α β : Type) : Type 1 → N → Prop` — **the one number in the
     encoding that is not read off the declaration**. The tag's constructors
     carry the index values as fields, so the tag must sit above every index
     type's own sort, and `γ : Type 1` is at `Sort 3`. A generator that wrote
     `max u (v+1)` and ignored the index sorts gets `Sort 1` and the kernel
     refuses the tag. Every other fixture in the tree is one where the cheap
     guess happens to be right: an index bound as a constructor field forces
     its sort below `u` for a `Type`-valued block, and a `Prop`-valued block's
     indices are usually `N`, at exactly `max 0 1`. This is a `Prop`-valued
     block indexed by a large type, which is neither. It also crosses two
     parameters with two indices, which nothing else here does.

     `γ` is a genuine index and not a promoted parameter because `SA.base` and
     `SC.base` give it the closed value `Type` while `step` gives it a variable.
   * `VA`/`VB (α : Type) : Pair α → Prop` — an index **type that mentions a
     parameter**. The index telescope is then not closed and has to be read at
     the parameter `fvar`s in scope rather than instantiated afterwards. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive PUnit : Sort u where
  | unit : PUnit

structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

inductive Bit : Type where
  | b0 : Bit
  | b1 : Bit

inductive Pair (α : Type) : Type where
  | mk : α → α → Pair α

--#export Eq N Bit Pair T0 T1 T2 MA MB MC DA DB SA SB SC VA VB
--#export t0Step maWrap mcFlat daStep dbMk saStep scBase vaStep vaBase

mutual
inductive T0 : N → Type where
  | base : T0 N.z
  | step : (n : N) → T2 n → T0 (N.s n)
inductive T1 : N → Type where
  | step : (n : N) → T0 n → T1 (N.s n)
inductive T2 : N → Type where
  | step : (n : N) → T1 n → T2 (N.s n)
end

mutual
/-- One index. -/
inductive MA : N → Type where
  | mk : MB → MA N.z
  | step : (n : N) → MC n → MA (N.s n)
/-- None. -/
inductive MB : Type where
  | base : MB
  | wrap : (n : N) → MA n → MB
/-- One again, so the block is not "the first member's telescope, then none". -/
inductive MC : N → Type where
  | mk : (n : N) → MA n → MC (N.s n)
  | flat : MB → MC N.z
end

mutual
/-- Indexed by `N`. -/
inductive DA : N → Type where
  | mk : DB Bit.b0 → DA N.z
  | step : (n : N) → DA n → DA (N.s n)
/-- Indexed by `Bit`, at the same sort. -/
inductive DB : Bit → Type where
  | base : DB Bit.b0
  | mk : (n : N) → DA n → DB Bit.b1
end

mutual
/-- Two parameters and two indices, the first of them at `Type 1`. -/
inductive SA (α : Type) (β : Type) : Type 1 → N → Prop where
  | base : α → SA α β Type N.z
  | step : (γ : Type 1) → (n : N) → SC α β γ n → SA α β γ (N.s n)
inductive SB (α : Type) (β : Type) : Type 1 → N → Prop where
  | step : (γ : Type 1) → (n : N) → SA α β γ n → SB α β γ (N.s n)
inductive SC (α : Type) (β : Type) : Type 1 → N → Prop where
  | base : β → SC α β Type N.z
  | step : (γ : Type 1) → (n : N) → SB α β γ n → SC α β γ (N.s n)
end

mutual
/-- An index whose *type* mentions the parameter. -/
inductive VA (α : Type) : Pair α → Prop where
  | base : (x : α) → VA α (Pair.mk x x)
  | step : (p : Pair α) → VB α p → VA α p
inductive VB (α : Type) : Pair α → Prop where
  | step : (p : Pair α) → VA α p → VB α p
end

def t0Step (n : N) (x : T2 n) : T0 (N.s n) := T0.step n x
def maWrap (n : N) (x : MA n) : MB := MB.wrap n x
def mcFlat (b : MB) : MC N.z := MC.flat b
def daStep (n : N) (x : DA n) : DA (N.s n) := DA.step n x
def dbMk (n : N) (x : DA n) : DB Bit.b1 := DB.mk n x
def saStep (α β : Type) (γ : Type 1) (n : N) (x : SC α β γ n) : SA α β γ (N.s n) := SA.step γ n x
def scBase (α β : Type) (b : β) : SC α β Type N.z := SC.base b
def vaStep (α : Type) (p : Pair α) (h : VB α p) : VA α p := VA.step p h
def vaBase (α : Type) (x : α) : VA α (Pair.mk x x) := VA.base x
