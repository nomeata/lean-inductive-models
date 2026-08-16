import InductiveModels.Simple.Site
import InductiveModels.Simple.Tight

/-!
# The field-preserving direct routes

The one-field, tight-pair and **indexed** models: the corner of the bare route
that keeps the constructor's fields rather than remembering only inhabitation.

All three store the fields in one place, [`InductiveModels.tightTowerTy`] —
which at one field *is* that field's type, so `.identity` is the tower too —
and they differ only in what sits around that storage: nothing, at `ni == 0`;
a `Prop`-valued packed equation naming the fibre, at `ni > 0`
([`InductiveModels.directIndexedModel`]). The indexed case used to be a
separate arm behind arm F in the dispatch chain, and there is no idea in it
this file did not already have.
-/

open Lean Meta

namespace InductiveModels

def primDirect (site : PrimSite) (directRoute : DirectRoute) (st : PrimOut) : GenM PrimOut := do
  -- The site, under the names this arm has always read it by.
  let tname := site.tname
  let lparams := site.lparams
  let np := site.np
  let memberTy := site.memberTy
  let exportCtors := site.exportCtors
  let selfN := site.selfN
  let recN := site.recN
  let ctorN := site.ctorN
  let declaredMemberTy := site.declaredMemberTy
  let ni := site.ni
  let w := site.w
  let rv := site.rv
  let v := site.v
  let eqi := site.eqi
  let installedRecTy := site.installedRecTy
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let mut out := st.out
  let mut spliced := st.spliced
  let mut projectionOverrides := st.projectionOverrides
  let (cn0, cty0) := exportCtors[0]!
  let modelCtorTy := publicSource cty0
  let (directDecls, directSpliced, overrides) ← emitDirectModel directRoute eqi tname
    lparams np ni cn0 memberTy cty0 modelCtorTy declaredMemberTy selfN (ctorN 0) recN
    rv.levelParams installedRecTy publicRecTy w v
  out := out ++ directDecls
  spliced := spliced ++ directSpliced
  projectionOverrides := projectionOverrides ++ overrides
  return { st with out, spliced, projectionOverrides }

end InductiveModels
