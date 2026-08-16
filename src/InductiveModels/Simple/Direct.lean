import InductiveModels.Simple.Site
import InductiveModels.Simple.Tight

/-!
# The field-preserving direct routes

The one-field and tight-pair models: the corner of the bare route that keeps
the constructor's fields rather than remembering only inhabitation.
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
  let (_, cty0) := exportCtors[0]!
  let modelCtorTy := publicSource cty0
  let (directDecls, directSpliced, overrides) ← emitDirectModel directRoute eqi tname
    lparams np memberTy cty0 modelCtorTy declaredMemberTy selfN (ctorN 0) recN
    rv.levelParams installedRecTy publicRecTy w v
  out := out ++ directDecls
  spliced := spliced ++ directSpliced
  projectionOverrides := projectionOverrides ++ overrides
  return { st with out, spliced, projectionOverrides }

end InductiveModels
