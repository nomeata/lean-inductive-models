/- **The sweep**: what else `mutual inductive` allows, asked rather than waited
   for.

   A claim that there is no shape Lean accepts and this refuses is worth exactly
   what was swept for it, and `nest_odd_shapes.lean` is the same idea for the
   nested construction. Each block here was written by asking what a `mutual`
   block may contain that the four fixtures beside it do not.

   * `LA`/`LB`/`LC` — a **`let` in a constructor field's type**. Lean accepts
     it, and the member a field sits at is then not the head of the expression
     as written.
   * `IA`/`IB`/`IC` — **implicit and strict-implicit binders** in the
     constructors, and a field that is a `Sort` rather than a value.
   * `WA`/`WB` — a **dependent index telescope**: the second index's type
     mentions the first. Every other indexed fixture here has independent
     indices, so an implementation that instantiated an index telescope at the
     wrong scope passes them and fails this.
   * `QA`/`QB` — an index whose type is a **parameter at a level parameter**,
     so the sort the tag has to live at is `max 1 (u+1)` and not a numeral. `W`
     is level-polymorphic exactly here.
   * `FA`/`FB` — a declaration **parameter that is a function type**, and a
     constructor field at it. -/
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

inductive Vec (α : Type) : N → Type where
  | nil : Vec α N.z
  | cons : (n : N) → α → Vec α n → Vec α (N.s n)

--#export Eq N Vec LA LB LC IA IB IC WA WB QA QB FA FB
--#export laMk lbOf icMk waMk wbBack qaMk faMk fbBack

mutual
/-- A `let` in the field's type. -/
inductive LA : Type where
  | mk : (n : N) → (let m := n; Vec N m) → LB → LA
inductive LB : Type where
  | of : LC → LB
inductive LC : Type where
  | z : LC
  | back : LA → LC
end

mutual
/-- Implicit and strict-implicit binders, and a `Sort`-valued field. -/
inductive IA : Type 1 where
  | mk : {α : Type} → ⦃β : Type⦄ → α → IB → IA
inductive IB : Type 1 where
  | mk : Type → IC → IB
inductive IC : Type 1 where
  | z : IC
  | back : IA → IC
end

mutual
/-- The second index's type mentions the first. -/
inductive WA : (n : N) → Vec N n → Type where
  | mk : (n : N) → (v : Vec N n) → WB n v → WA n v
inductive WB : (n : N) → Vec N n → Type where
  | z : (n : N) → (v : Vec N n) → WB n v
  | back : (n : N) → (v : Vec N n) → WA n v → WB n v
end

mutual
/-- An index at a parameter, so the tag's sort is `max 1 (u+1)`. -/
inductive QA (α : Type u) : α → Type u where
  | mk : (a : α) → QB α a → QA α a
inductive QB (α : Type u) : α → Type u where
  | z : (a : α) → QB α a
  | back : (a : α) → QA α a → QB α a
end

mutual
/-- A parameter that is a function type. -/
inductive FA (f : N → Type) : Type where
  | mk : (n : N) → f n → FB f → FA f
inductive FB (f : N → Type) : Type where
  | z : FB f
  | back : FA f → FB f
end

def laMk (n : N) (v : Vec N n) (b : LB) : LA := LA.mk n v b
def lbOf (c : LC) : LB := LB.of c
def icMk (a : IA) : IC := IC.back a
def waMk (n : N) (v : Vec N n) (b : WB n v) : WA n v := WA.mk n v b
def wbBack (n : N) (v : Vec N n) (a : WA n v) : WB n v := WB.back n v a
def qaMk (α : Type u) (a : α) (b : QB α a) : QA α a := QA.mk a b
def faMk (f : N → Type) (n : N) (x : f n) (b : FB f) : FA f := FA.mk n x b
def fbBack (f : N → Type) (a : FA f) : FB f := FB.back a
