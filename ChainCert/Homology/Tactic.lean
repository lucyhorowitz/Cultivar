import ChainCert.Homology.Basic
import ChainCert.Homology.MatrixReflect
import ChainCert.SNF.Tactic
import Lean.Elab.Tactic

open Lean Elab Tactic Meta Expr

/-!
# Homology tactic

The `homology` tactic computes a certified presentation for simplicial homology
over `ℤ`.

For a finite facet complex `X` and dimension `k`, the tactic builds a
certificate for:

```lean
ker (boundaryK (R := ℤ) X k) / im (boundaryK (R := ℤ) X (k + 1))
```

as a top-level value of type:

```lean
CertificateHomology (R := ℤ) X k
```

Internally, this includes a `ChainQuotientCert` containing SNF certificates for
`∂ₖ` and for the cycle-presentation matrix.

## User syntax

* `homology X, k`

  If the goal is definitionally equal to
  `CertificateHomology (R := ℤ) X k`, the tactic closes it. Otherwise, it adds
  a local hypothesis named `homologyCert` and leaves the goal unchanged.

* `homology X, k as h`

  Always adds a local hypothesis with the chosen name:

  ```lean
  h : CertificateHomology (R := ℤ) X k
  ```

The lower-level quotient certificate is available as `h.quotientCert`.

## Requirements

`X` must elaborate as `FiniteFacetComplex ι`, and `k` must elaborate as `Nat`.
The boundary matrices must be evaluable by the same SNF backend used by the
`snf` tactic.
-/

/--
Compute a certified simplicial homology presentation over `ℤ`.

Examples:

```lean
example : CertificateHomology (R := ℤ) X k := by
  homology X, k

example : True := by
  homology X, k as h
  -- h : CertificateHomology (R := ℤ) X k
  exact trivial
```
-/
syntax (name := homologyTac) "homology " term ", " term (" as " ident)? : tactic
syntax (name := homologyCertCmd) "homology_cert " term ", " term " as " ident : command

structure HomologyWitnessPayload where
  snfK : SnfSageJsonPayload
  MRows : List (List Int)
  snfM : SnfSageJsonPayload

private def snfPayloadFromObject (j : Lean.Json) : TacticM SnfSageJsonPayload := do
  let U ← IO.ofExcept (j.getObjVal? "U")
  let Uinv ← IO.ofExcept (j.getObjVal? "Uinv")
  let D ← IO.ofExcept (j.getObjVal? "D")
  let V ← IO.ofExcept (j.getObjVal? "V")
  let Vinv ← IO.ofExcept (j.getObjVal? "Vinv")
  pure { U := U, Uinv := Uinv, D := D, V := V, Vinv := Vinv }

private def callHomologyWitnesses (XExpr kExpr : Expr) :
    TacticM HomologyWitnessPayload := do
  let dim ← evalNatSafe kExpr
  let rawExpr ← mkAppM ``FiniteFacetComplex.toRawFacets #[XExpr]
  let rows ← ChainCert.profileStep "homology: evaluate raw facets" <|
    evalRawFacetStringListSafe rawExpr
  let facetsStr := stringListToMatString rows
  if chainCert.profile.get (← getOptions) then
    logInfo m!"[chainCert.profile] homology: {rows.length} facets, dim {dim}"
  let json ← ChainCert.profileStep "homology: Sage homology witnesses" <| do
    let reqJson := Lean.Json.mkObj [
      ("op", Lean.Json.str "homology"),
      ("facets", Lean.Json.str facetsStr),
      ("dim", Lean.Json.num dim),
      ("reduced", Lean.Json.bool false),
      ("base_ring", Lean.Json.str "ZZ"),
      ("witnesses", Lean.Json.bool true)
    ]
    sendSageRequest reqJson
  let snfKJson ← IO.ofExcept (json.getObjVal? "snf_k")
  let MJson ← IO.ofExcept (json.getObjVal? "M")
  let snfMJson ← IO.ofExcept (json.getObjVal? "snf_M")
  let (snfK, MRows, snfM) ← ChainCert.profileStep "homology: decode Sage payloads" <| do
    let snfK ← snfPayloadFromObject snfKJson
    let MRows ← ChainCert.SageDecode.decodeIntMatrix MJson
    let snfM ← snfPayloadFromObject snfMJson
    pure (snfK, MRows, snfM)
  pure { snfK := snfK, MRows := MRows, snfM := snfM }

private def matrixFinDims (e : Expr) : TacticM (Expr × Expr) := do
  let ty ← inferType e
  let (``Matrix, #[finM, finN, _R]) := ty.getAppFnArgs
    | throwError "homology: expected matrix expression, got {ty}"
  let (``Fin, #[mExpr]) := finM.getAppFnArgs
    | throwError "homology: expected row index type `Fin m`, got {finM}"
  let (``Fin, #[nExpr]) := finN.getAppFnArgs
    | throwError "homology: expected col index type `Fin n`, got {finN}"
  pure (mExpr, nExpr)

private def intMatrixExprFromRowsLike (rows : List (List Int)) (likeExpr : Expr) :
    TacticM Expr := do
  let (mExpr, nExpr) ← matrixFinDims likeExpr
  let rowsExpr ← ChainCert.intRowsToExpr rows
  mkAppM ``ChainCert.SageDecode.rowsToMatrix #[rowsExpr, mExpr, nExpr]

private def decodeIntRowsFromStrings (rows : List (List String)) : TacticM (List (List Int)) :=
  rows.mapM fun row =>
    row.mapM fun s =>
      match s.toInt? with
      | some z => pure z
      | none => throwError "homology: failed to decode Sage entry `{s}` as ring `ZZ`"

private def mkPresentationEqProof
    (MExpr cycleMExpr certK dk1Expr : Expr)
    (witnessPayload : HomologyWitnessPayload) : TacticM Expr := do
  let (nExpr, pExpr) ← matrixFinDims dk1Expr
  let rExpr ← mkAppM ``CertificateSNF.r #[certK]
  let vinvRows ← ChainCert.SageDecode.decodeIntMatrix witnessPayload.snfK.Vinv
  let dk1Rows ← decodeIntRowsFromStrings (← evalMatStringListSafe dk1Expr)
  let VinvRowsExpr ← ChainCert.intRowsToExpr vinvRows
  let Dk1RowsExpr ← ChainCert.intRowsToExpr dk1Rows
  let MRowsExpr ← ChainCert.intRowsToExpr witnessPayload.MRows
  let rowsToM ← mkAppM ``ChainCert.SageDecode.rowsToMatrix #[
    MRowsExpr, ← mkAppM ``Nat.sub #[nExpr, rExpr], pExpr]
  unless (← isDefEq MExpr rowsToM) do
    throwError "homology: internal error, Sage presentation matrix expression mismatch"
  let hRTy ← mkAppM ``LE.le #[rExpr, nExpr]
  let hR ← Lean.Elab.Tactic.elabNativeDecideCore `homology hRTy
  let dk1RowsMatrix ←
    mkAppM ``ChainCert.SageDecode.rowsToMatrix #[Dk1RowsExpr, nExpr, pExpr]
  let hDk1Ty ← mkEq dk1Expr dk1RowsMatrix
  let hDk1 ← Lean.Elab.Tactic.elabNativeDecideCore `homology hDk1Ty
  let checkExpr ← mkAppM ``ChainCert.Reflect.cyclePresentationRowsB
    #[VinvRowsExpr, Dk1RowsExpr, MRowsExpr, rExpr, nExpr, pExpr]
  let hCheckTy ← mkEq checkExpr (toExpr true)
  let hCheck ← Lean.Elab.Tactic.elabNativeDecideCore `homology hCheckTy
  let h ← mkAppM
    ``ChainCert.Reflect.rowsToMatrix_eq_cyclePresentationMatrix_of_cyclePresentationRowsB
      #[hR, hDk1, hCheck]
  let hTy ← inferType h
  let hMTy ← mkEq MExpr cycleMExpr
  unless (← isDefEq hTy hMTy) do
    throwError
      "homology: internal error constructing reflected presentation matrix equality\n\
      actual: {hTy}\n\
      expected: {hMTy}"
  pure h

private def addAbbrevDecl (name : Name) (type value : Expr) : Term.TermElabM Unit := do
  addAndCompile <| Declaration.defnDecl
    { name := name
      levelParams := []
      safety := DefinitionSafety.safe
      hints := ReducibilityHints.regular 0
      type := ← instantiateMVars type
      value := ← instantiateMVars value }

private def runTacticAsTerm (x : TacticM α) : Term.TermElabM α := do
  let (a, _) ← x { elaborator := `homology_cert, recover := false } |>.run { goals := [] }
  pure a

private def scopedName (n : Name) : Term.TermElabM Name := do
  if n.isInternal then
    pure n
  else
    return (← getCurrNamespace) ++ n

elab_rules : command
| `(homology_cert $XStx:term, $kStx:term as $h:ident) =>
  Lean.Elab.Command.liftTermElabM do
    let baseName ← scopedName h.getId
    let XExpr ← Term.elabTerm XStx none
    let kExpr ← Term.elabTerm kStx (some (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing

    let XTy ← inferType XExpr
    let (``FiniteFacetComplex, #[ιExpr]) := XTy.getAppFnArgs
      | throwError "homology_cert: expected `X : FiniteFacetComplex ι`, got {XTy}"

    let kTy ← inferType kExpr
    unless (← isDefEq kTy (mkConst ``Nat)) do
      throwError "homology_cert: expected `k : Nat`, got {kTy}"

    let k1Expr ← mkAppM ``Nat.succ #[kExpr]
    let dkExpr ← mkAppOptM ``boundaryK #[
      some (mkConst ``Int), none, none, none, none, none, some XExpr, some kExpr]
    let dk1Expr ← mkAppOptM ``boundaryK #[
      some (mkConst ``Int), none, none, none, none, none, some XExpr, some k1Expr]

    let witnessPayload ←
      runTacticAsTerm (callHomologyWitnesses XExpr kExpr)

    let dkName := baseName.str "dk"
    let dkTy ← inferType dkExpr
    logInfo m!"homology_cert: adding {dkName}"
    addAbbrevDecl dkName dkTy dkExpr
    let dkConst := mkConst dkName

    let dk1Name := baseName.str "dk1"
    let dk1Ty ← inferType dk1Expr
    logInfo m!"homology_cert: adding {dk1Name}"
    addAbbrevDecl dk1Name dk1Ty dk1Expr
    let dk1Const := mkConst dk1Name

    let certKName := baseName.str "certK"
    logInfo m!"homology_cert: adding {certKName}"
    let certKConst ← declareSNFCertFromPayload certKName dkConst witnessPayload.snfK

    let cycleMExpr ← mkAppM ``cyclePresentationMatrix #[certKConst, dk1Const]
    let MExpr ← runTacticAsTerm <|
      intMatrixExprFromRowsLike witnessPayload.MRows cycleMExpr
    let MName := baseName.str "M"
    let MTy ← inferType MExpr
    logInfo m!"homology_cert: adding {MName}"
    addAbbrevDecl MName MTy MExpr
    let MConst := mkConst MName

    let certMName := baseName.str "certM"
    logInfo m!"homology_cert: adding {certMName}"
    let certMConst ← declareSNFCertFromPayload certMName MConst witnessPayload.snfM

    let prodExpr ← mkAppM ``HMul.hMul #[dkConst, dk1Const]
    let prodTy ← inferType prodExpr
    let zeroTy ← mkAppM ``Zero #[prodTy]
    let zeroInst ← synthInstance zeroTy
    let zeroExpr ← mkAppOptM ``Zero.zero #[some prodTy, some zeroInst]
    let hCCTy ← mkEq prodExpr zeroExpr
    let hCC ← mkAppM ``CertificateHomology.boundaryK_comp_eq_zero_int #[XExpr, kExpr]
    unless (← isDefEq (← inferType hCC) hCCTy) do
      throwError "homology: internal error constructing chain condition proof"

    let hMTy ← mkEq MConst cycleMExpr
    let hM ← runTacticAsTerm <|
      mkPresentationEqProof MConst cycleMExpr certKConst dk1Const witnessPayload
    unless (← isDefEq (← inferType hM) hMTy) do
      throwError "homology_cert: internal error constructing presentation matrix equality"

    let qcExpr ← mkAppOptM ``ChainQuotientCert.mk #[
      none, none, none,
      some (mkConst ``Int),
      none, none,
      some dkConst,
      some dk1Const,
      some certKConst,
      some hCC,
      some MConst,
      some hM,
      some certMConst]

    let finalExpr ← mkAppOptM ``CertificateHomology.mk #[
      some (mkConst ``Int),
      none, none,
      some ιExpr,
      none, none, none,
      some XExpr,
      some kExpr,
      some qcExpr]

    let finalTy ← mkAppOptM ``CertificateHomology #[
      some (mkConst ``Int),
      none, none,
      some ιExpr,
      none, none, none,
      some XExpr,
      some kExpr]
    logInfo m!"homology_cert: adding {baseName}"
    addAbbrevDecl baseName finalTy finalExpr

@[tactic homologyTac] def evalHomologyTac : Tactic := fun stx => do
  let (certName, XStx, kStx) ←
    match stx with
    | `(tactic| homology $X:term, $k:term as $h:ident) => pure (h.getId, X, k)
    | `(tactic| homology $X:term, $k:term) => pure (`homologyCert, X, k)
    | _ => throwUnsupportedSyntax

  let XExpr ← elabTerm XStx none
  let kExpr ← elabTerm kStx (some (mkConst ``Nat))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

  -- sanity checks
  let XTy ← inferType XExpr
  let (``FiniteFacetComplex, #[ιExpr]) := XTy.getAppFnArgs
    | throwError "homology: expected `X : FiniteFacetComplex ι`, got {XTy}"

  let kTy ← inferType kExpr
  unless (← isDefEq kTy (mkConst ``Nat)) do
    throwError "homology: expected `k : Nat`, got {kTy}"

  let k1Expr ← mkAppM ``Nat.succ #[kExpr]

  let dkExpr ← mkAppOptM ``boundaryK #[
    some (mkConst ``Int), none, none, none, none, none, some XExpr, some kExpr]
  let dk1Expr ← mkAppOptM ``boundaryK #[
    some (mkConst ``Int), none, none, none, none, none, some XExpr, some k1Expr]

  let witnessPayload ← callHomologyWitnesses XExpr kExpr

  let certK ← ChainCert.profileStep "homology: build ∂k SNF certificate" <|
    mkSNFCertExprFromPayload dkExpr witnessPayload.snfK

  let cycleMExpr ← ChainCert.profileStep "homology: build cycle presentation matrix expr" <|
    mkAppM ``cyclePresentationMatrix #[certK, dk1Expr]
  let MExpr ← ChainCert.profileStep "homology: build Sage presentation matrix expr" <|
    intMatrixExprFromRowsLike witnessPayload.MRows cycleMExpr
  let certM ← ChainCert.profileStep "homology: build presentation SNF certificate" <|
    mkSNFCertExprFromPayload MExpr witnessPayload.snfM

  let hCC ← ChainCert.profileStep "homology: build chain-condition proof" <| do
    let prodExpr ← mkAppM ``HMul.hMul #[dkExpr, dk1Expr]
    let prodTy ← inferType prodExpr
    let zeroTy ← mkAppM ``Zero #[prodTy]
    let zeroInst ← synthInstance zeroTy
    let zeroExpr ← mkAppOptM ``Zero.zero #[some prodTy, some zeroInst]
    let hCCTy ← mkEq prodExpr zeroExpr
    let hCC ← mkAppM ``CertificateHomology.boundaryK_comp_eq_zero_int #[XExpr, kExpr]
    unless (← isDefEq (← inferType hCC) hCCTy) do
      throwError "homology: internal error constructing chain condition proof"
    pure hCC

  let hM ← ChainCert.profileStep "homology: build presentation equality proof" <| do
    mkPresentationEqProof MExpr cycleMExpr certK dk1Expr witnessPayload

  let qcExpr ← ChainCert.profileStep "homology: assemble quotient certificate" <|
    mkAppOptM ``ChainQuotientCert.mk #[
    none, none, none,        -- m n p
    some (mkConst ``Int),    -- R
    none, none,              -- instances
    some dkExpr,
    some dk1Expr,
    some certK,
    some hCC,
    some MExpr,
    some hM,
    some certM]

  let homologyCertExpr ← ChainCert.profileStep "homology: assemble homology certificate" <|
    mkAppOptM ``CertificateHomology.mk #[
    some (mkConst ``Int),
    none, none,
    some ιExpr,
    none, none, none,
    some XExpr,
    some kExpr,
    some qcExpr
  ]

  let hcTy ← mkAppOptM ``CertificateHomology #[
    some (mkConst ``Int),
    none, none,
    some ιExpr,
    none, none, none,
    some XExpr,
    some kExpr
  ]

  let goal ← getMainGoal

  ChainCert.profileStep "homology: assign/note certificate" <| do
    if certName == `homologyCert then
      let target ← goal.getType
      if ← isDefEq target hcTy then
        goal.assign homologyCertExpr
        setGoals []
      else
        let (_, goal') ← goal.note certName homologyCertExpr (some hcTy)
        setGoals [goal']
    else
      let (_, goal') ← goal.note certName homologyCertExpr (some hcTy)
      setGoals [goal']
