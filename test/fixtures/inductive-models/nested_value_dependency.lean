/-
Whether a constructor field can depend on the *value* of a field whose type
mentions the owner family (a recursive or nested occurrence).

That shape is the only way a projection rule for an occurrence-free field
could still need transport, because the modeled projection of an occurrence
field is not the source field on the nose.  Lean's kernel makes the shape
unwritable, so the class this fixture guards is empty:

* Reading a nested field needs a function on the container, and nesting has
  already rewritten the container away.  `mk (l : List T) (h : P l.length)`
  is `(kernel) application type mismatch ... argument has type
  `_nested.List_1` but function has type `List T → Nat``, and `T × Nat` with
  `p.2` and `Option T` with `Option.map` fail identically.
* Reading the field with a *polymorphic* function instead instantiates that
  function at `T`: `mk (t : T) (h : P (f t))` is `(kernel) arg #2 of `T.mk`
  contains a non valid occurrence of the datatypes being declared`.
* Naming the value in an inductive family has the same effect one level up:
  `mk (t : T) (h : Eq t t)` is `(kernel) invalid nested inductive datatype
  `Eq`, nested inductive datatypes parameters cannot contain local
  variables`, and so is `Fin l.length` before its argument is even reached.
* No field can supply the missing function either: `mk (f : T → Type)
  (t : T) (x : f t)` is a non-positive occurrence.
* A `Prop` owner is closed twice over, because a container of proofs has no
  large elimination to a type family in the first place.

That leaves a head beta-redex that discards the occurrence field, which the
kernel contracts before export.  `NestedVacuous` and `RecursiveVacuous` pin
that: their exported constructors have no dependency left at all.
`NestedEarly` and `NestedLate` are the dependencies that do occur, depending
on an occurrence-free field on either side of the nested one, and `PlainDep`
and `RecursiveDep` are their occurrence-free and directly recursive controls.
-/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive Idx where
  | here
  | elsewhere

inductive Box (α : Type u) : Type u where
  | mk (value : α) : Box α

/-- A nested occurrence followed by the only field type that may mention it:
one whose head beta-redex discards the occurrence field. -/
inductive NestedVacuous : Type where
  | mk (b : Box NestedVacuous) (h : (fun _ => Idx) b) : NestedVacuous

/-- The plain recursive analogue of `NestedVacuous`. -/
inductive RecursiveVacuous : Type where
  | mk (t : RecursiveVacuous) (h : (fun _ => Idx) t) : RecursiveVacuous

/-- A genuine dependency after the nested occurrence.  Its type mentions the
occurrence-free field `n`, never the nested field `b`. -/
inductive NestedEarly (fam : Idx → Type) : Type where
  | mk (b : Box (NestedEarly fam)) (n : Idx) (h : fam n) : NestedEarly fam

/-- The same genuine dependency before the nested occurrence. -/
inductive NestedLate (fam : Idx → Type) : Type where
  | mk (n : Idx) (h : fam n) (b : Box (NestedLate fam)) : NestedLate fam

/-- Occurrence-free control for the same genuine dependency. -/
inductive PlainDep (fam : Idx → Type) : Type where
  | mk (n : Idx) (h : fam n) : PlainDep fam

/-- Direct-recursion control for the same genuine dependency. -/
inductive RecursiveDep (fam : Idx → Type) : Type where
  | mk (n : Idx) (h : fam n) (t : RecursiveDep fam) : RecursiveDep fam

--#export Eq Idx Box NestedVacuous RecursiveVacuous NestedEarly NestedLate
--#export PlainDep RecursiveDep
