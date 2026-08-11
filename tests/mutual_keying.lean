/- **A file that has already taken a name the model wants.**

   §1 fixes the model's names, so a consumer keys on them — and a file is free
   to declare one of them itself. `mini/tests/fixtures/nested_keying.lean` is
   this for the nested construction and this is it for the mutual one:
   `KB._model.self` is declared *after* the block, so a guard that looked only
   at the environment as it stands would generate a second one and emit an
   export with a duplicate declaration. The guard scans the whole input file.

   `KB` and not `KA`, deliberately: the model's namespace is the **first**
   member's (`KA._model`) but the carriers are one per member
   (`KA._model.self`, `KB._model.self`), so a guard that only checked names
   under the namespace it writes into would miss this one.

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

/-- The name the model wants for `KB`'s carrier, declared by the file itself
    and **after** the block. -/
def KB._model.self : Type := N

def kaOf (b : KB) : KA := KA.mk b
def gaOf (b : GB) : GA := GA.mk b
