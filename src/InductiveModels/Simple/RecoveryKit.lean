import InductiveModels.Simple.Church

/-!
# The recovery arm's zipper

Walking the indexed subsingleton's constructor telescope while recovering its
dependent data fields from the caller's index telescope.
-/

open Lean Meta

namespace InductiveModels

/-- Walk the recovery arm's constructor telescope while recovering dependent data fields
from the caller's index telescope.  Before each moving pivot, a packed equality
of the complete earlier index prefix transports the caller's pivot back to the
constructor field type.  Proof fields are then bound at the already recovered
constructor prefix. -/
partial def recoveryZipPrefix (eqi : EqInfo) (memberTy ctorTy : Expr) (ni : Nat)
    (isData : Array Bool) (idxPos : Array Nat) (transports : Array (Nat × Nat))
    (ps is : Array Expr) (ctorIdx : Expr → GenM (Array Expr))
    (bind : Nat → Name → Expr → (Expr → GenM Expr) → GenM Expr)
    (k : Array Expr → Array Expr → Array Expr → GenM Expr) : GenM Expr := do
  let indexPackAt := fun (sel : Array Nat) => do
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun opened _ => do
      let (pk, ℓ) ← packTyAt opened sel 0
      pure (pk.replaceFVars opened is, ℓ)
  let indexTypeAt := fun (full : Array Expr) (position : Nat) => do
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun opened _ => do
      pure ((← ityp opened[position]!).replaceFVars opened full)
  let tele ← instForall ctorTy ps
  let nf := numForalls tele
  forallBoundedTelescope tele (some nf) fun raw res => do
    let rawIdx ← ctorIdx res
    let rec go (i slot : Nat) (fields bound : Array Expr) : GenM Expr := do
      if i == nf then
        let resolved := rawIdx.map (·.replaceFVars raw fields)
        return ← k fields bound resolved
      if isData[i]! then
        let position := idxPos[i]!
        if transports.contains (i, position) then
          let sel := Array.range position
          if sel.isEmpty then
            badShape s!"a transported pivot at index {position} has no prefix"
          let (pk, ℓpk) ← indexPackAt sel
          let previous := raw.extract 0 i
          let lhsValues := sel.map fun j => rawIdx[j]!.replaceFVars previous fields
          for value in lhsValues do
            for later in raw.extract i raw.size do
              if value.containsFVar later.fvarId! then
                badShape s!"a transported pivot at index {position} has a constructor prefix depending on an unrecovered field"
          let lhs ← packChain position pk lhsValues 0
          let rhs ← packChain position pk (sel.map (is[·]!)) 0
          bind slot `prefix_eq (eqi.mk' ℓpk pk lhs rhs) fun h => do
            let hs ← symmOf eqi ℓpk pk lhs rhs h
            let base := is[position]!
            let pv ← ilevel (← indexTypeAt is position)
            let field ← transportAlong eqi pv ℓpk pk rhs lhs hs base fun y => do
              let ys ← unpackChain position pk y
              let mut full := is
              for j in [0:position] do full := full.set! j ys[j]!
              indexTypeAt full position
            go (i + 1) (slot + 1) (fields.push field) (bound.push h)
        else
          go (i + 1) slot (fields.push is[position]!) bound
      else
        let ft := (← ityp raw[i]!).replaceFVars (raw.extract 0 i) fields
        bind slot (Name.mkSimple s!"field_{i}") ft fun field =>
          go (i + 1) (slot + 1) (fields.push field) (bound.push field)
    go 0 0 #[] #[]

def recoveryZipMinor (eqi : EqInfo) (memberTy ctorTy : Expr) (ni : Nat)
    (isData : Array Bool) (idxPos : Array Nat) (transports : Array (Nat × Nat))
    (ps is : Array Expr) (pk : Expr) (ℓpk : Level)
    (ctorIdx : Expr → GenM (Array Expr)) (mk : Array Expr → Expr → GenM Expr)
    (k : Array Expr → Expr → GenM Expr) : GenM Expr := do
  let sel := Array.range ni
  recoveryZipPrefix eqi memberTy ctorTy ni isData idxPos transports ps is ctorIdx
    (fun _ name ty cont => withLocalDeclD name ty cont)
    fun fs bnd idx => do
      let lhs ← packChain ni pk (sel.map (idx[·]!)) 0
      let rhs ← packChain ni pk (sel.map (is[·]!)) 0
      withLocalDeclD `heq (eqi.mk' ℓpk pk lhs rhs) fun h => do
        mk (bnd.push h) (← k fs h)

def recoveryZipCtorArgs (eqi : EqInfo) (memberTy : Expr) (ni : Nat)
    (isData : Array Bool) (idxPos : Array Nat) (transports : Array (Nat × Nat))
    (ps idx fields : Array Expr) (pk : Expr) (ℓpk : Level) : GenM (Array Expr) := do
  let nf := isData.size
  let mut args : Array Expr := #[]
  for i in [0:nf] do
    if isData[i]! then
      let position := idxPos[i]!
      if transports.contains (i, position) then
        let sel := Array.range position
        let (prefixPk, ℓprefix) ←
          forallBoundedTelescope (← instForall memberTy ps) (some ni) fun opened _ => do
            let (pk, ℓ) ← packTyAt opened sel 0
            pure (pk.replaceFVars opened idx, ℓ)
        let packed ← packChain position prefixPk (sel.map (idx[·]!)) 0
        args := args.push (eqi.refl' ℓprefix prefixPk packed)
    else
      args := args.push fields[i]!
  let packed ← packChain ni pk ((Array.range ni).map (idx[·]!)) 0
  pure (args.push (eqi.refl' ℓpk pk packed))

/-- The recovery arm's full-index zipper recursor.  The outer equality moves the entire
dependent index telescope.  Its motive is a function over every prefix
equation and proof field, so the constructor endpoint applies the original
minor while the caller endpoint rebuilds exactly the Church witness stored in
the major premise. -/
def recoveryZipRec (eqi : EqInfo) (ℓpk : Level) (lift? : Option Level)
    (pk pkc pki heq motive minor : Expr) (idxs : Array Expr)
    (zipAll : Array Expr → (Array Expr → Array Expr → GenM Expr) → GenM Expr)
    (minorTy : Array Expr → Expr → GenM Expr)
    (encodedAt : Array Expr → GenM Expr) (extracted : Array Expr) : GenM Expr := do
  let fam := fun (y : Expr) (_h : Expr) => do
    let full ← unpackChain idxs.size pk y
    zipAll full fun _ args => do
      let rebuilt ← withLocalDeclD `r (.sort .zero) fun r => do
        withLocalDeclD `k (← minorTy full r) fun kk =>
          mkLambdaFVars #[r, kk] (mkAppN kk args)
      let lifted ← match lift? with
        | none => pure rebuilt
        | some ℓ => pure (puliftUp ℓ (← encodedAt full) rebuilt)
      mkForallFVars args (mkAppN motive (full.push lifted))
  let motiveE ← withLocalDeclD `y pk fun y => do
    withLocalDeclD `hy (eqi.mk' ℓpk pk pkc y) fun hy => do
      mkLambdaFVars #[y, hy] (← fam y hy)
  let endpoint ← unpackChain idxs.size pk pkc
  let base ← zipAll endpoint fun fields args =>
    mkLambdaFVars args (mkAppN minor fields)
  let fn := eqi.recAt (← ilevel (← inferType base)) ℓpk pk pkc motiveE base pki heq
  pure (mkAppN fn extracted)

/-- Extract the recovery arm's zipper premises from the Church major and hand them to the
full-index equality recursor.  Kept out of [`InductiveModels.primIso`] so the route
dispatcher remains below the default elaboration heartbeat budget. -/
def recoveryZipModelRec (eqi : EqInfo) (lift? : Option Level)
    (memberTy ctorTy : Expr) (ni : Nat) (isData : Array Bool) (idxPos : Array Nat)
    (transports : Array (Nat × Nat)) (ps idxs : Array Expr) (base pk motive minor : Expr)
    (ℓpk : Level) (ctorIdx : Expr → GenM (Array Expr))
    (minorTy : Array Expr → Expr → GenM Expr)
    (encodedAt : Array Expr → GenM Expr) : GenM Expr := do
  let packSel := Array.range ni
  let project := fun (slot : Nat) => do
    recoveryZipPrefix eqi memberTy ctorTy ni isData idxPos transports ps idxs ctorIdx
      (fun _ name ty cont => withLocalDeclD name ty cont)
      fun _ bnd idx => do
        let lhs ← packChain ni pk (packSel.map (idx[·]!)) 0
        let rhs ← packChain ni pk (packSel.map (idxs[·]!)) 0
        withLocalDeclD `heq (eqi.mk' ℓpk pk lhs rhs) fun h => do
          mkLambdaFVars (bnd.push h) (if slot == bnd.size then h else bnd[slot]!)
  recoveryZipPrefix eqi memberTy ctorTy ni isData idxPos transports ps idxs ctorIdx
    (fun slot _ ty cont => do
      let value := mkAppN base #[ty, ← project slot]
      cont value)
    fun _ args idxE => do
      let pkc ← packChain ni pk (packSel.map (idxE[·]!)) 0
      let pki ← packChain ni pk (packSel.map (idxs[·]!)) 0
      let eqTy := eqi.mk' ℓpk pk pkc pki
      let heq := mkAppN base #[eqTy, ← project args.size]
      recoveryZipRec eqi ℓpk lift? pk pkc pki heq motive minor idxs
        (fun full kk =>
          recoveryZipPrefix eqi memberTy ctorTy ni isData idxPos transports ps full ctorIdx
            (fun _ name ty cont => withLocalDeclD name ty cont)
            fun fs bnd idx => do
              let lhs ← packChain ni pk (packSel.map (idx[·]!)) 0
              let rhs ← packChain ni pk (packSel.map (full[·]!)) 0
              withLocalDeclD `heq (eqi.mk' ℓpk pk lhs rhs) fun h =>
                kk fs (bnd.push h))
        minorTy encodedAt (args.push heq)

end InductiveModels
