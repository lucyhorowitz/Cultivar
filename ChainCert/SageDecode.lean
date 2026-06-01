-- SageDecode.lean
-- Incoming deserialization: how raw JSON responses from the Sage server
-- are turned into Lean-level data. Sage encodes integer matrix entries as
-- strings (so arbitrary-precision ints survive JSON round-tripping), so
-- decoders here handle both the JSON shape and the `String → Int` parse.

import Lean
import Mathlib.LinearAlgebra.Matrix.Defs
import ChainCert.SageEncode

open Lean

namespace ChainCert.SageDecode

/-- Decode a JSON value that is expected to be an array of arrays of strings
    into a `List (List String)`. Throws if the shape is wrong. -/
def decodeStringMatrix (j : Json) : MetaM (List (List String)) := do
  let rows ← IO.ofExcept j.getArr?
  rows.toList.mapM fun row => do
    let cells ← IO.ofExcept row.getArr?
    cells.toList.mapM fun cell => IO.ofExcept cell.getStr?

/-- Decode a JSON value that is expected to be an array of arrays of decimal
    integer strings into a `List (List Int)`. Sage serializes matrix entries
    as strings to avoid JSON number-precision issues; this parses them back. -/
def decodeIntMatrix (j : Json) : MetaM (List (List Int)) := do
  let rows ← decodeStringMatrix j
  rows.mapM fun row =>
    row.mapM fun s =>
      match s.toInt? with
      | some n => pure n
      | none => throwError s!"failed to parse integer from {s}"

/-- Decode a JSON value that is expected to be an array of arrays of natural
    numbers into a `List (List Nat)`. Used for simplex bases (`domain_basis`,
    `codomain_basis`) returned by the `boundary` op, where entries are JSON
    numbers rather than strings. -/
def decodeNatMatrix (j : Json) : MetaM (List (List Nat)) := do
  let rows ← IO.ofExcept j.getArr?
  rows.toList.mapM fun row => do
    let cells ← IO.ofExcept row.getArr?
    cells.toList.mapM fun cell => IO.ofExcept cell.getNat?

/-- Build a `Matrix (Fin m) (Fin n) ℤ` from a `List (List Int)` by treating
    the outer list as rows and the inner lists as entries. Out-of-bounds
    lookups return 0, so if the list is ragged or undersized the matrix
    is zero-padded. -/
def toIntMatrix (rows : List (List Int)) (m n : ℕ) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j => (rows.getD i.val [] |>.getD j.val 0 : Int)

def mkIntExpr (z : Int) : Expr :=
  if z ≥ 0 then
    mkApp (mkConst ``Int.ofNat) (mkRawNatLit z.toNat)
  else
    mkApp (mkConst ``Int.negSucc) (mkRawNatLit (z.natAbs - 1))

def decodeSerializableMatrix
    {R : Type} [SageSerializable R]
    (j : Lean.Json) : MetaM (List (List R)) := do
  let rows ← ChainCert.SageDecode.decodeStringMatrix j
  rows.mapM fun row =>
    row.mapM fun s =>
      match SageSerializable.fromSageString (R := R) s with
      | some r => pure r
      | none => throwError s!"snf: failed to decode `{s}` as {SageSerializable.sageName (R := R)}"

/-- Build a matrix from row-major list data, zero-padding out-of-bounds accesses. -/
def rowsToMatrix {R : Type} [Zero R] (rows : List (List R)) (m n : Nat) :
    Matrix (Fin m) (Fin n) R :=
  fun i j => (rows.getD i.val [] |>.getD j.val 0)

/-- Build an expression for `rowsToMatrix rows m n` from an expression
`rows : List (List R)` and type expression `R`. -/
def matrixExprOfRows
    (R rows : Expr) (m n : Nat) : MetaM Expr := do
  let zeroTy ← Lean.Meta.mkAppM ``Zero #[R]
  let _zeroInst ← Lean.Meta.synthInstance zeroTy
  Lean.Meta.mkAppM ``rowsToMatrix #[rows, mkRawNatLit m, mkRawNatLit n]


end ChainCert.SageDecode
