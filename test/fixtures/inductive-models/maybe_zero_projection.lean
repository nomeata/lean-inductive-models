/- **One-constructor owners at a maybe-zero sort whose payload the model
   must retain.**

   A lifted Church carrier is a subsingleton, so it cannot support a
   projection which returns constructor data at a positive instantiation of
   `u`. Unindexed nonrecursive owners therefore use Direct; unindexed owners
   with a bare recursive field use the Empty construction.

   Indexed nonliteral-`Prop` owners use Carve. `MZIdx` and `MZIdx2` exercise
   nonrecursive data fields. `MZIdxRecursive` combines a data projection with
   an indexed recursive child: its skeleton supplies the child data, while
   small elimination on the relational `Good` proof supplies the child's
   fibre evidence. `MZProof` is the large-elimination control whose proof
   field is recovered directly from the index construction; `MZOne` is the
   Direct control.

   `MZSelf` and `MZData` are the Empty cases. Their constructors already
   require an inhabitant of the type being defined, so the carrier may end in
   the exact-sort lift of Church `False`; `MZData` stores its nonrecursive
   field in front of that empty tail. All requested projection rules remain
   on their literal constructor fields and are checked by the generated
   kernel fixture. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u

inductive Eq : {a : Sort u} → a → a → Prop where
  | refl (x : a) : Eq x x

inductive Nt : Type where
  | z : Nt
  | s : Nt → Nt

inductive MZOne (a : Sort u) : Sort u where
  | mk : a → MZOne a

inductive MZProof (p : Prop) (n : Nt) : Nt → Sort u where
  | mk : p → MZProof p n n

inductive MZSelf : Sort u where
  | mk : MZSelf → MZSelf

inductive MZData (a : Sort u) : Sort u where
  | mk : a → MZData a → MZData a

inductive MZIdx (a : Sort u) (n : Nt) : Nt → Sort u where
  | mk : a → MZIdx a n n

inductive MZIdx2 (a : Sort u) (b : Sort u) (n : Nt) : Nt → Sort u where
  | mk : a → b → MZIdx2 a b n n

/- The indexed corner combines the two obligations that used to be split
   between the storage and Church routes: retain a data field for projection,
   and carry an indexed recursive child through the recursor. -/
inductive MZIdxRecursive (a : Sort u) (n : Nt) : Nt → Sort u where
  | mk : a → MZIdxRecursive a n n → MZIdxRecursive a n n
