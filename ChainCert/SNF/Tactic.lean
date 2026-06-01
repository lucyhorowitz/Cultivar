import ChainCert.SNF.Core
import ChainCert.SNF.Verify
import ChainCert.SNF.Rank
import ChainCert.SageServer
import ChainCert.SageEncode
import ChainCert.SageDecode
import ChainCert.MatrixReflect
import Lean.Elab.Tactic
import Lean

/-!
# SNF tactic

The `snf` tactic computes and certifies Smith normal form data for a concrete
matrix.

## User syntax

* `snf A`

  Adds a local hypothesis named `cert`:

  ```lean
  cert : CertificateSNF A
  ```

* `snf A as hA`

  Adds the same certificate under the chosen name:

  ```lean
  hA : CertificateSNF A
  ```

The tactic is goal-agnostic: it enriches the local context and leaves the
current goal unchanged.

## Requirements

The matrix must have type:

```lean
Matrix (Fin m) (Fin n) R
```

where its entries can be serialized through `SageSerializable R`. The matrix
data must be evaluable at elaboration time; fully symbolic matrix variables are
not supported.

Dimensions may be non-literal expressions such as `cellCount X k`. The tactic
serializes entries by compiled evaluation, asks Sage for SNF data, reconstructs
the matrices in Lean, and builds a `CertificateSNF A` term checked by Lean.
-/

open Lean Elab Tactic Meta Expr

register_option chainCert.profile : Bool := {
  defValue := false
  descr := "print timing information for ChainCert elaborator/tactic stages"
}

def ChainCert.profileStep (label : String) (x : TacticM α) : TacticM α := do
  if chainCert.profile.get (← getOptions) then
    logInfo m!"[chainCert.profile] start {label}"
    let start ← IO.monoMsNow
    let a ← x
    let elapsed := (← IO.monoMsNow) - start
    logInfo m!"[chainCert.profile] done  {label}: {elapsed}ms"
    pure a
  else
    x

structure SnfSageJsonPayload where
  U : Lean.Json
  Uinv : Lean.Json
  D : Lean.Json
  V : Lean.Json
  Vinv : Lean.Json

/-- Extract `(finM, finN, mExpr, nExpr, R)` from the type of `AExpr : Matrix (Fin m) (Fin n) R`.
`mExpr`/`nExpr` are the natural-valued Exprs inside the `Fin _` applications; they
need *not* reduce to concrete Nat literals. -/
private def ensureSnfInput (AExpr : Expr) :
    TacticM (Expr × Expr × Expr × Expr × Expr) := do
  let AType ← inferType AExpr
  let (``Matrix, #[finM, finN, R]) := AType.getAppFnArgs
    | throwError "snf: expected `Matrix (Fin m) (Fin n) R`, got {AType}"

  let (``Fin, #[mExpr]) := finM.getAppFnArgs
    | throwError "snf: expected row index type `Fin m`, got {finM}"
  let (``Fin, #[nExpr]) := finN.getAppFnArgs
    | throwError "snf: expected col index type `Fin n`, got {finN}"

  if AExpr.hasMVar then
    throwError "snf: matrix must be concrete/closed (contains metavariables)"

  let sageSerializableTy ← mkAppM ``SageSerializable #[R]
  let _inst ← synthInstance sageSerializableTy

  pure (finM, finN, mExpr, nExpr, R)

private def certTypeFor (AExpr : Expr) : MetaM Expr :=
  mkAppM ``CertificateSNF #[AExpr]

/-- Assert `certName : CertificateSNF AExpr := certExpr` into the main goal context,
returning the new goal mvar. -/
private def addCertToContext
    (goal : MVarId) (certName : Name) (AExpr certExpr : Expr) :
    TacticM MVarId := do
  let certTy ← certTypeFor AExpr
  let certExprTy ← inferType certExpr
  unless (← isDefEq certExprTy certTy) do
    throwError "snf: internal error, certificate term has type {certExprTy}, expected {certTy}"
  let (_, goal') ← goal.note certName certExpr (some certTy)
  pure goal'

/-- Call Sage for SNF. Serializes `A` via `matStringList` → `evalMatStringListSafe`
(compiled-code path; does not require `Fin` dims to reduce in the kernel). -/
private def callSnfSageJson (AExpr : Expr) : TacticM SnfSageJsonPayload := do
  let rows ← ChainCert.profileStep "snf: evaluate input matrix" <| evalMatStringListSafe AExpr
  let matStr := stringListToMatString rows
  if chainCert.profile.get (← getOptions) then
    let cols := rows.head?.map (·.length) |>.getD 0
    logInfo m!"[chainCert.profile] snf: input matrix {rows.length} x {cols}"
  let json ← ChainCert.profileStep "snf: Sage request" <| do
    let reqJson := Lean.Json.mkObj [
      ("op", Lean.Json.str "snf"),
      ("matrix", Lean.Json.str matStr)
    ]
    sendSageRequest reqJson
  let U ← IO.ofExcept (json.getObjVal? "U")
  let Uinv ← IO.ofExcept (json.getObjVal? "Uinv")
  let D ← IO.ofExcept (json.getObjVal? "D")
  let V ← IO.ofExcept (json.getObjVal? "V")
  let Vinv ← IO.ofExcept (json.getObjVal? "Vinv")
  pure { U := U, Uinv := Uinv, D := D, V := V, Vinv := Vinv }

unsafe def evalBoolExpr (e : Expr) : MetaM Bool :=
  Lean.Meta.evalExpr Bool (mkConst ``Bool) e

@[implemented_by evalBoolExpr]
opaque evalBoolExprSafe (e : Expr) : MetaM Bool

unsafe def evalStringExpr (e : Expr) : MetaM String :=
  Lean.Meta.evalExpr String (mkConst ``String []) e

@[implemented_by evalStringExpr]
opaque evalStringExprSafe (e : Expr) : MetaM String

private def parseSerializableElemExpr (R : Expr) (s : String) : TacticM Expr := do
  if (← isDefEq R (mkConst ``Int)) then
    match s.toInt? with
    | some z => return mkIntLit z
    | none => throwError "snf: failed to decode Sage entry `{s}` as ring `ZZ`"
  let serializableTy ← mkAppM ``SageSerializable #[R]
  let serializableInst ← synthInstance serializableTy
  let parseExpr ← mkAppOptM ``SageSerializable.fromSageString
    #[some R, some serializableInst, some (mkStrLit s)]
  let isSomeExpr ← mkAppM ``Option.isSome #[parseExpr]
  let ok ← evalBoolExprSafe isSomeExpr
  unless ok do
    let sageNameExpr ← mkAppOptM ``SageSerializable.sageName #[some R, some serializableInst]
    let ringName ← evalStringExprSafe sageNameExpr
    throwError "snf: failed to decode Sage entry `{s}` as ring `{ringName}`"
  let zeroTy ← mkAppM ``Zero #[R]
  let zeroInst ← synthInstance zeroTy
  let zeroExpr ← mkAppOptM ``Zero.zero #[some R, some zeroInst]
  mkAppOptM ``Option.getD #[some R, some parseExpr, some zeroExpr]

private def decodeSerializableRowsExpr
    (R : Expr) (j : Lean.Json) : TacticM (List (List Expr)) := do
  let rows ← ChainCert.SageDecode.decodeStringMatrix j
  rows.mapM fun row => row.mapM (parseSerializableElemExpr R)

private def decodeIntRowsFromStrings (rows : List (List String)) : TacticM (List (List Int)) :=
  rows.mapM fun row =>
    row.mapM fun s =>
      match s.toInt? with
      | some z => pure z
      | none => throwError "snf: failed to decode Sage entry `{s}` as ring `ZZ`"

private def mulRows (A B : List (List Int)) (m n p : Nat) : List (List Int) :=
  (List.range m).map fun i =>
    (List.range p).map fun j =>
      ((List.range n).map fun k =>
        (A.getD i []).getD k 0 * (B.getD k []).getD j 0).sum

private def mkListExpr (α : Expr) (xs : List Expr) : TacticM Expr := do
  let nilExpr ← mkAppOptM ``List.nil #[some α]
  xs.foldrM
    (fun x acc => mkAppOptM ``List.cons #[some α, some x, some acc])
    nilExpr

def ChainCert.intRowsToExpr (rows : List (List Int)) : TacticM Expr := do
  let intTy := mkConst ``Int
  let listIntTy ← mkAppM ``List #[intTy]
  let rowExprs ← rows.mapM fun row => do
    let entries := row.map mkIntLit
    mkListExpr intTy entries
  mkListExpr listIntTy rowExprs

/-- Build `Matrix finM finN R` as an Expr, reusing existing `Fin _` Exprs directly. -/
private def matrixTyExprFromFin (R finM finN : Expr) : MetaM Expr :=
  mkAppM ``Matrix #[finM, finN, R]

private def ensureMatrixExprHasType (matrixExpr expectedTy : Expr) : TacticM Unit := do
  let gotTy ← inferType matrixExpr
  unless (← isDefEq gotTy expectedTy) do
    throwError "snf: internal error, matrix expression has type {gotTy}, expected {expectedTy}"

private def mkZeroOfType (α : Expr) : TacticM Expr := do
  let zeroTy ← mkAppM ``Zero #[α]
  let zeroInst ← synthInstance zeroTy
  mkAppOptM ``Zero.zero #[some α, some zeroInst]

private def mkOneOfType (α : Expr) : TacticM Expr := do
  let oneTy ← mkAppM ``One #[α]
  let oneInst ← synthInstance oneTy
  mkAppOptM ``One.one #[some α, some oneInst]

private def mkMulExpr (a b : Expr) : TacticM Expr :=
  mkAppM ``HMul.hMul #[a, b]

private def mkFirstZeroDiagExpr (D : Expr) : TacticM Expr :=
  mkAppM ``firstZeroDiag #[D]

private def mkDecideProofExpr (p : Expr) : TacticM Expr :=
  Lean.Elab.Tactic.elabNativeDecideCore `snf p

private def addRegularDefDecl (name : Name) (type value : Expr) :
    Lean.Elab.Term.TermElabM Unit := do
  addAndCompile <| Declaration.defnDecl
    { name := name
      levelParams := []
      safety := DefinitionSafety.safe
      hints := ReducibilityHints.regular 0
      type := ← instantiateMVars type
      value := ← instantiateMVars value }

private def runTacticAsTerm (elaborator : Name) (x : TacticM α) :
    Lean.Elab.Term.TermElabM α := do
  let (a, _) ← x { elaborator := elaborator, recover := false } |>.run { goals := [] }
  pure a

private def mkVerifyDiagProofExpr (DExpr : Expr) : TacticM Expr := do
  let hTy ← mkAppM ``verifyDiag #[DExpr]
  mkDecideProofExpr hTy

private def mkHdiagProofExpr (DExpr hVerify : Expr) : TacticM Expr :=
  mkAppM ``ChainCert.SNF.isDiagonal_of_verifyDiag #[DExpr, hVerify]

private def mkHdivProofExpr (_DExpr hVerify : Expr) : TacticM Expr :=
  pure (mkProj ``And 1 hVerify)

private def mkDivChainWithinRankExpr (mExpr nExpr R DExpr : Expr) : TacticM Expr := do
  let dvdInst ← synthInstance (← mkAppM ``Dvd #[R])
  let zeroInst ← synthInstance (← mkAppM ``Zero #[R])
  let decEqInst ← synthInstance (← mkAppM ``DecidableEq #[R])
  mkAppOptM ``divChainWithinRank #[
    some mExpr, some nExpr, some R, some dvdInst, some zeroInst, some decEqInst, some DExpr]

private def mkRankProofExpr (mExpr nExpr DExpr hVerify : Expr) : TacticM Expr := do
  let minExpr ← mkAppM ``Nat.min #[mExpr, nExpr]
  let finMinTy ← mkAppM ``Fin #[minExpr]
  withLocalDeclD `i finMinTy fun i => do
    let theoremExpr ←
      mkAppM ``ChainCert.SNF.diagEntry_eq_zero_iff_ge_firstZeroDiag_of_verifyDiag
        #[DExpr, i, hVerify]
    mkLambdaFVars #[i] theoremExpr

private def mkDivisibilityProofType (mExpr nExpr DExpr : Expr) : TacticM Expr := do
  let minExpr ← mkAppM ``Nat.min #[mExpr, nExpr]
  let finMinTy ← mkAppM ``Fin #[minExpr]
  withLocalDeclD `i finMinTy fun i => do
    withLocalDeclD `j finMinTy fun j => do
      let iVal ← mkAppM ``Fin.val #[i]
      let jVal ← mkAppM ``Fin.val #[j]
      let iSucc ← mkAppM ``Nat.succ #[iVal]
      let hTy ← mkEq iSucc jVal
      withLocalDeclD `h hTy fun h => do
        let cutoff ← mkAppM ``firstZeroDiag #[DExpr]
        let hjTy ← mkAppM ``LT.lt #[jVal, cutoff]
        withLocalDeclD `hj hjTy fun hj => do
          let diagI ← mkAppM ``diagEntry #[DExpr, i]
          let diagJ ← mkAppM ``diagEntry #[DExpr, j]
          let body ← mkAppM ``Dvd.dvd #[diagI, diagJ]
          mkForallFVars #[i, j, h, hj] body

/-- Build a `CertificateSNF AExpr` expression from already available Sage SNF
JSON, then elaborate and type-check it. -/
def mkSNFCertExprFromPayload (AExpr : Expr) (payload : SnfSageJsonPayload) :
    TacticM Expr := do
  let (_finM, _finN, mExpr, nExpr, R) ←
    ChainCert.profileStep "snf cert: inspect input type" <| ensureSnfInput AExpr
  let ⟨uJson, uinvJson, dJson, vJson, vinvJson⟩ := payload
  let (uEntriesExpr, uinvEntriesExpr, dEntriesExpr, vEntriesExpr, vinvEntriesExpr) ←
    ChainCert.profileStep "snf cert: decode payload matrices" <| do
      let uEntriesExpr ← decodeSerializableRowsExpr R uJson
      let uinvEntriesExpr ← decodeSerializableRowsExpr R uinvJson
      let dEntriesExpr ← decodeSerializableRowsExpr R dJson
      let vEntriesExpr ← decodeSerializableRowsExpr R vJson
      let vinvEntriesExpr ← decodeSerializableRowsExpr R vinvJson
      pure (uEntriesExpr, uinvEntriesExpr, dEntriesExpr, vEntriesExpr, vinvEntriesExpr)

  let intTy := mkConst ``Int
  let listIntTy ← mkAppM ``List #[intTy]          -- Expr for `List Int`

  let (URowsExpr, UExpr, UinvRowsExpr, UinvExpr, DRowsExpr, DExpr,
      VRowsExpr, VExpr, VinvRowsExpr, VinvExpr) ←
    ChainCert.profileStep "snf cert: build witness matrix expressions" <| do
      let URowExprs ← uEntriesExpr.mapM (fun row => mkListExpr intTy row)
      let URowsExpr ← mkListExpr listIntTy URowExprs
      let UExpr ← mkAppM ``ChainCert.SageDecode.rowsToMatrix #[URowsExpr, mExpr, mExpr]
      let UinvRowExprs ← uinvEntriesExpr.mapM (fun row => mkListExpr intTy row)
      let UinvRowsExpr ← mkListExpr listIntTy UinvRowExprs
      let UinvExpr ← mkAppM ``ChainCert.SageDecode.rowsToMatrix #[UinvRowsExpr, mExpr, mExpr]
      let DRowExprs ← dEntriesExpr.mapM (fun row => mkListExpr intTy row)
      let DRowsExpr ← mkListExpr listIntTy DRowExprs
      let DExpr ← mkAppM ``ChainCert.SageDecode.rowsToMatrix #[DRowsExpr, mExpr, nExpr]
      let VRowExprs ← vEntriesExpr.mapM (fun row => mkListExpr intTy row)
      let VRowsExpr ← mkListExpr listIntTy VRowExprs
      let VExpr ← mkAppM ``ChainCert.SageDecode.rowsToMatrix #[VRowsExpr, nExpr, nExpr]
      let VinvRowExprs ← vinvEntriesExpr.mapM (fun row => mkListExpr intTy row)
      let VinvRowsExpr ← mkListExpr listIntTy VinvRowExprs
      let VinvExpr ← mkAppM ``ChainCert.SageDecode.rowsToMatrix #[VinvRowsExpr, nExpr, nExpr]
      pure (URowsExpr, UExpr, UinvRowsExpr, UinvExpr, DRowsExpr, DExpr,
        VRowsExpr, VExpr, VinvRowsExpr, VinvExpr)

  let (ARowsExpr, UARowsExpr) ← ChainCert.profileStep "snf cert: build reflected row data" <| do
    let mVal ← evalNatSafe mExpr
    let nVal ← evalNatSafe nExpr
    let uRows ← ChainCert.SageDecode.decodeIntMatrix uJson
    let aRows ← decodeIntRowsFromStrings (← evalMatStringListSafe AExpr)
    let uaRows := mulRows uRows aRows mVal mVal nVal
    let ARowsExpr ← ChainCert.intRowsToExpr aRows
    let UARowsExpr ← ChainCert.intRowsToExpr uaRows
    pure (ARowsExpr, UARowsExpr)

  let rExpr ← mkAppM ``firstZeroDiag #[DExpr]

  let hVerify ← ChainCert.profileStep "snf cert: prove verifyDiag" <|
    mkVerifyDiagProofExpr DExpr
  let hdiagExpr ← ChainCert.profileStep "snf cert: build hdiag" <|
    mkHdiagProofExpr DExpr hVerify
  let hrankExpr ← ChainCert.profileStep "snf cert: build hrank" <|
    mkRankProofExpr mExpr nExpr DExpr hVerify

  let trueExpr := toExpr true

  let hUUinvExpr ← ChainCert.profileStep "snf cert: prove U inverse" <| do
    let UbExpr ← mkAppM ``ChainCert.Reflect.mulIsOneB #[
      URowsExpr, UinvRowsExpr, mExpr, mExpr]
    let UbTrue ← mkEq UbExpr trueExpr
    let hUb ← mkDecideProofExpr UbTrue
    mkAppM ``ChainCert.Reflect.rowsToMatrix_mul_eq_one #[hUb]

  let hVVinvExpr ← ChainCert.profileStep "snf cert: prove V inverse" <| do
    let VbExpr ← mkAppM ``ChainCert.Reflect.mulIsOneB #[
      VRowsExpr, VinvRowsExpr, nExpr, nExpr]
    let VbTrue ← mkEq VbExpr trueExpr
    let hVb ← mkDecideProofExpr VbTrue
    mkAppM ``ChainCert.Reflect.rowsToMatrix_mul_eq_one #[hVb]

  let (_heqTy, heqExpr) ← ChainCert.profileStep "snf cert: prove U*A*V = D" <| do
    let UAExpr ← mkMulExpr UExpr AExpr
    let UAVExpr ← mkMulExpr UAExpr VExpr
    let heqTy ← mkEq UAVExpr DExpr
    let AMatrixExpr ← mkAppM ``ChainCert.SageDecode.rowsToMatrix #[ARowsExpr, mExpr, nExpr]
    let hATy ← mkEq AExpr AMatrixExpr
    let hAExpr ← mkDecideProofExpr hATy
    let UAbExpr ← mkAppM ``ChainCert.Reflect.mulEqB
      #[URowsExpr, ARowsExpr, UARowsExpr, mExpr, mExpr, nExpr]
    let UAbTrue ← mkEq UAbExpr trueExpr
    let hUAb ← mkDecideProofExpr UAbTrue
    let UAVbExpr ← mkAppM ``ChainCert.Reflect.mulEqB
      #[UARowsExpr, VRowsExpr, DRowsExpr, mExpr, nExpr, nExpr]
    let UAVbTrue ← mkEq UAVbExpr trueExpr
    let hUAVb ← mkDecideProofExpr UAVbTrue
    let heqExpr ← mkAppM ``ChainCert.Reflect.rowsToMatrix_mul_matrix_mul_eq_of_mulEqB
      #[hAExpr, hUAb, hUAVb]
    unless (← isDefEq (← inferType heqExpr) heqTy) do
      throwError "snf: internal error constructing reflected triple-product proof"
    pure (heqTy, heqExpr)

  let hdivExpr ← ChainCert.profileStep "snf cert: build hdiv" <|
    mkHdivProofExpr DExpr hVerify

  let certExpr ← ChainCert.profileStep "snf cert: assemble certificate" <|
    mkAppOptM ``CertificateSNF.mk #[
    some mExpr, some nExpr,
    some R,
    none, none,
    some AExpr,
    some UExpr,
    some UinvExpr,
    some VExpr,
    some VinvExpr,
    some DExpr,
    some rExpr,
    some (← mkEqRefl rExpr),
    some hdiagExpr,
    some hrankExpr,
    some hUUinvExpr,
    some hVVinvExpr,
    some heqExpr,
    some hdivExpr
  ]

  pure certExpr

/-- Declare an SNF certificate as a family of named definitions.

This is intended for command elaborators that need a persistent certificate for
larger matrices. Naming the witness matrices first keeps Lean from checking one
large inlined certificate term. -/
def declareSNFCertFromPayload (baseName : Name) (AExpr : Expr)
    (payload : SnfSageJsonPayload) : Lean.Elab.Term.TermElabM Expr := do
  logInfo m!"snf decl: decoding {baseName}"
  let (finM, finN, mExpr, nExpr, R, UExpr, UinvExpr, DExpr, VExpr, VinvExpr) ←
    runTacticAsTerm `snf do
      let (finM, finN, mExpr, nExpr, R) ← ensureSnfInput AExpr
      let ⟨uJson, uinvJson, dJson, vJson, vinvJson⟩ := payload
      let uEntriesExpr ←  decodeSerializableRowsExpr R uJson
      let uinvEntriesExpr ←  decodeSerializableRowsExpr R uinvJson
      let dEntriesExpr ←  decodeSerializableRowsExpr R dJson
      let vEntriesExpr ←  decodeSerializableRowsExpr R vJson
      let vinvEntriesExpr ←  decodeSerializableRowsExpr R vinvJson
      let intTy := mkConst ``Int
      let listIntTy ← mkAppM ``List #[intTy]
      let toMatrix (entries : List (List Expr)) (rowsDim colsDim : Expr) : TacticM Expr := do
        let rowExprs ← entries.mapM (fun row => mkListExpr intTy row)
        let rowsExpr ← mkListExpr listIntTy rowExprs
        mkAppM ``ChainCert.SageDecode.rowsToMatrix #[rowsExpr, rowsDim, colsDim]
      let UExpr ← toMatrix uEntriesExpr mExpr mExpr
      let UinvExpr ← toMatrix uinvEntriesExpr mExpr mExpr
      let DExpr ← toMatrix dEntriesExpr mExpr nExpr
      let VExpr ← toMatrix vEntriesExpr nExpr nExpr
      let VinvExpr ← toMatrix vinvEntriesExpr nExpr nExpr
      pure (finM, finN, mExpr, nExpr, R, UExpr, UinvExpr, DExpr, VExpr, VinvExpr)

  let matMMTy ← matrixTyExprFromFin R finM finM
  let matMNTy ← matrixTyExprFromFin R finM finN
  let matNNTy ← matrixTyExprFromFin R finN finN

  let ⟨uJson, uinvJson, dJson, vJson, vinvJson⟩ := payload
  let mVal ← runTacticAsTerm `snf (evalNatSafe mExpr)
  let nVal ← runTacticAsTerm `snf (evalNatSafe nExpr)
  let uRows ← ChainCert.SageDecode.decodeIntMatrix uJson
  let uinvRows ← ChainCert.SageDecode.decodeIntMatrix uinvJson
  let dRows ← ChainCert.SageDecode.decodeIntMatrix dJson
  let vRows ← ChainCert.SageDecode.decodeIntMatrix vJson
  let vinvRows ← ChainCert.SageDecode.decodeIntMatrix vinvJson
  let aRows ← runTacticAsTerm `snf do
    decodeIntRowsFromStrings (← evalMatStringListSafe AExpr)
  let uaRows := mulRows uRows aRows mVal mVal nVal
  let URowsExpr ← runTacticAsTerm `snf (ChainCert.intRowsToExpr uRows)
  let UinvRowsExpr ← runTacticAsTerm `snf (ChainCert.intRowsToExpr uinvRows)
  let DRowsExpr ← runTacticAsTerm `snf (ChainCert.intRowsToExpr dRows)
  let VRowsExpr ← runTacticAsTerm `snf (ChainCert.intRowsToExpr vRows)
  let VinvRowsExpr ← runTacticAsTerm `snf (ChainCert.intRowsToExpr vinvRows)
  let ARowsExpr ← runTacticAsTerm `snf (ChainCert.intRowsToExpr aRows)
  let UARowsExpr ← runTacticAsTerm `snf (ChainCert.intRowsToExpr uaRows)
  let trueExpr := toExpr true

  let UName := baseName.str "U"
  logInfo m!"snf decl: adding {UName}"
  addRegularDefDecl UName matMMTy UExpr
  let UConst := mkConst UName

  let UinvName := baseName.str "Uinv"
  logInfo m!"snf decl: adding {UinvName}"
  addRegularDefDecl UinvName matMMTy UinvExpr
  let UinvConst := mkConst UinvName

  let DName := baseName.str "D"
  logInfo m!"snf decl: adding {DName}"
  addRegularDefDecl DName matMNTy DExpr
  let DConst := mkConst DName

  let VName := baseName.str "V"
  logInfo m!"snf decl: adding {VName}"
  addRegularDefDecl VName matNNTy VExpr
  let VConst := mkConst VName

  let VinvName := baseName.str "Vinv"
  logInfo m!"snf decl: adding {VinvName}"
  addRegularDefDecl VinvName matNNTy VinvExpr
  let VinvConst := mkConst VinvName

  let rName := baseName.str "r"
  let rExpr ← mkAppM ``firstZeroDiag #[DConst]
  logInfo m!"snf decl: adding {rName}"
  addRegularDefDecl rName (mkConst ``Nat) rExpr
  let rConst := mkConst rName

  let hVerifyName := baseName.str "hVerify"
  logInfo m!"snf decl: adding {hVerifyName}"
  let hVerifyTy ← mkAppM ``verifyDiag #[DConst]
  let hVerifyExpr ← runTacticAsTerm `snf (mkDecideProofExpr hVerifyTy)
  addRegularDefDecl hVerifyName hVerifyTy hVerifyExpr
  let hVerifyConst := mkConst hVerifyName

  let hdiagName := baseName.str "hdiag"
  logInfo m!"snf decl: adding {hdiagName}"
  let hdiagExpr ← runTacticAsTerm `snf (mkHdiagProofExpr DConst hVerifyConst)
  let hdiagTy ← inferType hdiagExpr
  addRegularDefDecl hdiagName hdiagTy hdiagExpr
  let hdiagConst := mkConst hdiagName

  let hrankName := baseName.str "hrank"
  logInfo m!"snf decl: adding {hrankName}"
  let hrankExpr ← runTacticAsTerm `snf (mkRankProofExpr mExpr nExpr DConst hVerifyConst)
  let hrankTy ← inferType hrankExpr
  addRegularDefDecl hrankName hrankTy hrankExpr
  let hrankConst := mkConst hrankName

  let hUUinvName := baseName.str "hUUinv"
  logInfo m!"snf decl: adding {hUUinvName}"
  let (hUUinvTy, hUUinvExpr) ← runTacticAsTerm `snf do
    let UUinvExpr ← mkMulExpr UConst UinvConst
    let oneMM ← mkOneOfType matMMTy
    let hUUinvTy ← mkEq UUinvExpr oneMM
    let bExpr ← mkAppM ``ChainCert.Reflect.mulIsOneB #[
      URowsExpr, UinvRowsExpr, mExpr, mExpr]
    let bTrue ← mkEq bExpr trueExpr
    let hb ← mkDecideProofExpr bTrue
    let hUUinvExpr ← mkAppM ``ChainCert.Reflect.rowsToMatrix_mul_eq_one #[hb]
    unless (← isDefEq (← inferType hUUinvExpr) hUUinvTy) do
      throwError "snf decl: internal error constructing reflected U inverse proof"
    pure (hUUinvTy, hUUinvExpr)
  addRegularDefDecl hUUinvName hUUinvTy hUUinvExpr
  let hUUinvConst := mkConst hUUinvName

  let hVVinvName := baseName.str "hVVinv"
  logInfo m!"snf decl: adding {hVVinvName}"
  let (hVVinvTy, hVVinvExpr) ← runTacticAsTerm `snf do
    let VVinvExpr ← mkMulExpr VConst VinvConst
    let oneNN ← mkOneOfType matNNTy
    let hVVinvTy ← mkEq VVinvExpr oneNN
    let bExpr ← mkAppM ``ChainCert.Reflect.mulIsOneB #[
      VRowsExpr, VinvRowsExpr, nExpr, nExpr]
    let bTrue ← mkEq bExpr trueExpr
    let hb ← mkDecideProofExpr bTrue
    let hVVinvExpr ← mkAppM ``ChainCert.Reflect.rowsToMatrix_mul_eq_one #[hb]
    unless (← isDefEq (← inferType hVVinvExpr) hVVinvTy) do
      throwError "snf decl: internal error constructing reflected V inverse proof"
    pure (hVVinvTy, hVVinvExpr)
  addRegularDefDecl hVVinvName hVVinvTy hVVinvExpr
  let hVVinvConst := mkConst hVVinvName

  let heqName := baseName.str "heq"
  logInfo m!"snf decl: adding {heqName}"
  let (heqTy, heqExpr) ← runTacticAsTerm `snf do
    let UAExpr ← mkMulExpr UConst AExpr
    let UAVExpr ← mkMulExpr UAExpr VConst
    let heqTy ← mkEq UAVExpr DConst
    let AMatrixExpr ←
      mkAppM ``ChainCert.SageDecode.rowsToMatrix #[ARowsExpr, mExpr, nExpr]
    let hATy ← mkEq AExpr AMatrixExpr
    let hAExpr ← mkDecideProofExpr hATy
    let UAbExpr ← mkAppM ``ChainCert.Reflect.mulEqB
      #[URowsExpr, ARowsExpr, UARowsExpr, mExpr, mExpr, nExpr]
    let UAbTrue ← mkEq UAbExpr trueExpr
    let hUAb ← mkDecideProofExpr UAbTrue
    let UAVbExpr ← mkAppM ``ChainCert.Reflect.mulEqB
      #[UARowsExpr, VRowsExpr, DRowsExpr, mExpr, nExpr, nExpr]
    let UAVbTrue ← mkEq UAVbExpr trueExpr
    let hUAVb ← mkDecideProofExpr UAVbTrue
    let heqExpr ← mkAppM
      ``ChainCert.Reflect.rowsToMatrix_mul_matrix_mul_eq_of_mulEqB
        #[hAExpr, hUAb, hUAVb]
    unless (← isDefEq (← inferType heqExpr) heqTy) do
      throwError "snf decl: internal error constructing reflected triple-product proof"
    pure (heqTy, heqExpr)
  addRegularDefDecl heqName heqTy heqExpr
  let heqConst := mkConst heqName

  let hdivName := baseName.str "hdiv"
  logInfo m!"snf decl: adding {hdivName}"
  let hdivExpr ← runTacticAsTerm `snf (mkHdivProofExpr DConst hVerifyConst)
  logInfo m!"snf decl: built {hdivName} proof"
  let hdivTy ← runTacticAsTerm `snf (mkDivChainWithinRankExpr mExpr nExpr R DConst)
  logInfo m!"snf decl: built {hdivName} type"
  logInfo m!"snf decl: adding {hdivName} def"
  addRegularDefDecl hdivName hdivTy hdivExpr
  let hdivConst := mkConst hdivName

  logInfo m!"snf decl: assembling {baseName}"
  let certExpr ← mkAppOptM ``CertificateSNF.mk #[
    some mExpr, some nExpr,
    some R,
    none, none,
    some AExpr,
    some UConst,
    some UinvConst,
    some VConst,
    some VinvConst,
    some DConst,
    some rConst,
    some (← mkEqRefl rConst),
    some hdiagConst,
    some hrankConst,
    some hUUinvConst,
    some hVVinvConst,
    some heqConst,
    some hdivConst
  ]
  let certTy ← certTypeFor AExpr
  logInfo m!"snf decl: adding {baseName}"
  addRegularDefDecl baseName certTy certExpr
  pure (mkConst baseName)

/-- Build a `CertificateSNF AExpr` expression from Sage data, then elaborate and
type-check it. This is the reusable construction backend for the `snf` tactic. -/
def mkSNFCertExpr (AExpr : Expr) : TacticM Expr := do
  let payload ← callSnfSageJson AExpr
  mkSNFCertExprFromPayload AExpr payload

/--
Compute a Smith normal form certificate for `A`.

Examples:

```lean
example : True := by
  snf A
  -- cert : CertificateSNF A
  trivial

example : True := by
  snf A as hA
  -- hA : CertificateSNF A
  trivial
```
-/
syntax (name := snfTac) "snf " term (" as " ident)? : tactic

@[tactic snfTac] def evalSnfTac : Tactic := fun stx => do
  let goal ← getMainGoal
  let some (certName, AStx) := (match stx with
    | `(tactic| snf $A as $h:ident) => some (h.getId, A)
    | `(tactic| snf $A) => some (`cert, A)
    | _ => none) |
    throwError "expected `snf A` or `snf A as h`"
  let AExpr ← elabTerm AStx none
  let certExpr ← mkSNFCertExpr AExpr
  let certExprTy ← inferType certExpr
  let certTy ← certTypeFor AExpr
  unless (← isDefEq certExprTy certTy) do
    throwError
      "snf: internal error, certificate term has wrong type\n\
      actual: {certExprTy}\n\
      expected: {certTy}"

  let goal' ← addCertToContext goal certName AExpr certExpr
  -- logInfo "snf: added `cert : CertificateSNF A` to local context."
  setGoals [goal']
