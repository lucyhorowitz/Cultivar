import ChainCert.SageDecode
import Mathlib.Data.Matrix.Mul

namespace ChainCert.Reflect

open ChainCert.SageDecode

def eqB (a b : List (List Int)) : Bool := a == b

lemma rowsToMatrix_eq_of_eqB {m n} {a b : List (List Int)}
    (h : eqB a b = true) :
    rowsToMatrix a m n = rowsToMatrix b m n := by
  have : a = b := by simpa [eqB] using h   -- via beq_iff_eq / eq_of_beq
  rw [this]

def mulEqB (A B D : List (List Int)) (m n p : Nat) : Bool :=
  (List.range m).all fun i =>
    (List.range p).all fun j =>
      (((List.range n).map fun k =>
          (A.getD i []).getD k 0 * (B.getD k []).getD j 0).sum
        == (D.getD i []).getD j 0)

lemma mulEqB_sound {m n p} {A B D : List (List Int)}
    (h : mulEqB A B D m n p = true) :
    rowsToMatrix A m n * rowsToMatrix B n p = rowsToMatrix D m p := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [rowsToMatrix]
  rw [Fin.sum_univ_eq_sum_range (fun k =>
        ((A.getD i.val []).getD (k) 0 * (B.getD k []).getD (↑j) 0))]
  simp only [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range,
              Multiset.map_coe, Multiset.sum_coe]
  unfold mulEqB at h
  simp_all

  -- LHS entry: rw [Matrix.mul_apply]  → ∑ k : Fin n, A i k * B k j
  -- now show that Finset.sum equals the List.range sum in `mulEqB`, then use h

def mulIsOneB (A B : List (List Int)) (m n : Nat) : Bool :=
  (List.range m).all fun i =>
    (List.range m).all fun j =>
      (((List.range n).map fun k =>
          (A.getD i []).getD k 0 * (B.getD k []).getD j 0).sum
        == (if i = j then 1 else 0))

lemma rowsToMatrix_mul_eq_one {m n} {A B : List (List Int)}
    (h : mulIsOneB A B m n = true) :
    rowsToMatrix A m n * rowsToMatrix B n m = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [rowsToMatrix]
  rw [Fin.sum_univ_eq_sum_range (fun k =>
        ((A.getD i.val []).getD (k) 0 * (B.getD k []).getD (↑j) 0))]
  simp only [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range,
              Multiset.map_coe, Multiset.sum_coe, Matrix.one_apply]
  unfold mulIsOneB at h
  simp_all
  omega


end ChainCert.Reflect
