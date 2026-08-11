/- Focused nested-imax storage cases.  The non-indexed family exercises the
   direct Type route; the indexed family exercises the same shape after arm C
   erases its index. -/

universe u v

inductive I : Type where
  | z : I

inductive BoxF (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | mk : ((α → β) → β) → BoxF α β

inductive IBox (α : Sort u) (β : Sort v) : I → Sort (max 1 u v) where
  | mk : ((α → β) → β) → IBox α β I.z

--#export Eq I BoxF IBox
