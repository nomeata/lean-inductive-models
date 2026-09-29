/- The two declarations every closed tower stream starts from: `Eq` and `Nat`,
   exported from Lean's own prelude.

   Upstream's `mk_tower_fixtures.py` writes streams that mention `Eq`,
   `Eq.refl`, `Nat` and `Nat.zero` without declaring them: con-leche supplies
   its own prelude, Lean's kernel does not. `test/scripts/mk_con_leche_towers.py`
   reads this export and writes each tower after it, reusing its table entries,
   so that every tower stream is a complete kernel export. -/

--#export Eq Nat
