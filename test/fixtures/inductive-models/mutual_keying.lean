/- **A file that has taken a legacy-looking model name.**

   `KB._model.self` is declared *after* the block. It used to collide with a
   carrier spelling, but is not a declaration-local contract name now. The
   exact-role guard must ignore it and generate both mutual models.

   `KB` and not `KA`, deliberately: this preserves the harder historical
   spelling and catches any accidental return to suffix-based keying.

   `GA`/`GB` in the same file is the atom that says the guard is not simply
   refusing everything. -/
prelude

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

--#export Eq N KA KB GA GB KB._model.self kaOf gaOf

mutual
inductive KA : Type where
  | mk : KB → KA
inductive KB : Type where
  | z : KB
  | back : KA → KB
end

mutual
inductive GA : Type where
  | mk : GB → GA
inductive GB : Type where
  | z : GB
  | back : GA → GB
end

/-- An obsolete carrier spelling, declared **after** the block and ignored. -/
def KB._model.self : Type := N

def kaOf (b : KB) : KA := KA.mk b
def gaOf (b : GB) : GA := GA.mk b
