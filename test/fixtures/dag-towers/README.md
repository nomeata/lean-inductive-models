# DAG towers

Expressions that are small as DAGs and astronomically large as trees, in every
record position this tool reads. Each tower is about 2^60 nodes with its
sharing expanded and a few hundred as a DAG, so any traversal that forgets
sharing does not finish: these fixtures are a gate on the *walkers*, as
[`docs/maintainers/DagSafety.md`](../../../docs/maintainers/DagSafety.md)
explains. [`expected.txt`](expected.txt) lists them; every one is a complete
kernel export that Lean's kernel accepts and that this tool must model within
the resource bound `test/scripts/check_fixture_verdicts.py` enforces.

* `tower_*.ndjson` are con-leche's tower fixtures
  (`scripts/mk_tower_fixtures.py` at con-leche revision
  `78ded4b6fc9a4d9ab809e8ca2c75c56537c41bff`, Apache License 2.0; see
  [`../con-leche/`](../con-leche/)), ported by
  [`test/scripts/mk_con_leche_towers.py`](../../scripts/mk_con_leche_towers.py).
  Upstream's streams rely on con-leche's built-in prelude; the port writes each
  one after `tower_basis.ndjson` — `Eq` and `Nat` as stock lean4export writes
  them from Lean's prelude (`tower_basis.lean`) — and hash-conses every table
  entry, and changes nothing else. Regenerate with
  `test/scripts/mk_con_leche_towers.py`.
* `ctor_field_towers.lean` is this repository's own: towers in the constructor
  fields of the owners the Simple route models — the shape of
  `EulerMeanVariationalInverse.StrongMeanEvolution` in the Lean Kernel Arena's
  `navier-stokes-euler` export — including a `Prod` tower of the kind its
  instance towers are, with an exported projection, and arrow towers, whose `Π`
  nodes nothing can reduce away. Its export is regenerated with
  `FIXTURE_DIR=$PWD/test/fixtures/dag-towers LEAN_INDUCTIVE_MODELS_FILTER=0 scripts/export-fixture.sh ctor_field_towers.lean`.
