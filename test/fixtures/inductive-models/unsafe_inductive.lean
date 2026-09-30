/- **`unsafe` inductive blocks are exempt: outside the logic, nothing to model.**

   Lean's kernel admits an `unsafe inductive` without its positivity check —
   `Bad` below recurses negatively — and forbids every safe declaration from
   naming one, so nothing an extensional consumer translates can depend on it.
   A model made of safe definitions is therefore never needed, and of `Bad` it
   would be a proof of `False`. The tool reports each such block as *exempt*,
   exactly as it reports the basis primitives — its own line, not a decline —
   and passes the records through unchanged. Lean Kernel Arena replay skips
   them the same way (`KernelCheck.replaySkipped`).

   One owner per route the block would otherwise have reached, so the
   exemption is shown to sit in front of all of them:

   * `Bad` — negative recursion, con-leche's `ind_unsafe`. It used to reach
     the simple route's shape analysis and stop there with an internal error.
   * `UTree` — a positive, ordinary shape, which a safe twin would model.
   * `UList` — nested (`numNested = 1`), the nested route.
   * `UA`/`UB` — a mutual block, the mutual route.

   `List` is the one safe inductive here and is modelled as usual.
-/

--#export-flags --export-unsafe
--#export Bad UTree UList UA UB

unsafe inductive Bad where
  | mk : (Bad → Nat) → Bad

unsafe inductive UTree where
  | leaf
  | node (l r : UTree)

unsafe inductive UList where
  | nil
  | cons (xs : List UList)

mutual
unsafe inductive UA where
  | a (b : UB)
  | z
unsafe inductive UB where
  | b (a : UA)
end
