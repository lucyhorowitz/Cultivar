import ChainCert.SageDecode
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range

namespace ChainCert.Reflect

open ChainCert.SageDecode

def eqB (a b : List (List Int)) : Bool := a == b

def rowsEqB (A B : List (List Int)) (m n : Nat) : Bool :=
  (List.range m).all fun i =>
    (List.range n).all fun j =>
      ((A.getD i []).getD j 0 == (B.getD i []).getD j 0)

def mulRows (A B : List (List Int)) (m n p : Nat) : List (List Int) :=
  (List.range m).map fun i =>
    (List.range p).map fun j =>
      ((List.range n).map fun k =>
        (A.getD i []).getD k 0 * (B.getD k []).getD j 0).sum

lemma rowsEqB_sound {m n} {A B : List (List Int)}
    (h : rowsEqB A B m n = true) :
    rowsToMatrix A m n = rowsToMatrix B m n := by
  ext i j
  unfold rowsToMatrix rowsEqB at *
  simp_all only [List.all_eq_true, List.mem_range]
  simpa using h i.val i.isLt j.val j.isLt

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

lemma mulRows_mulEqB (A B : List (List Int)) (m n p : Nat) :
    mulEqB A B (mulRows A B m n p) m n p = true := by
  unfold mulEqB mulRows
  simp only [List.all_eq_true, List.mem_range]
  intro i hi j hj
  have hrow : i < ((List.range m).map
      (fun i =>
        (List.range p).map fun j =>
          ((List.range n).map fun k =>
            (A.getD i []).getD k 0 * (B.getD k []).getD j 0).sum)).length := by
    simpa using hi
  rw [List.getD_eq_getElem (l := (List.range m).map
      (fun i =>
        (List.range p).map fun j =>
          ((List.range n).map fun k =>
            (A.getD i []).getD k 0 * (B.getD k []).getD j 0).sum))
      (d := []) hrow]
  simp only [List.getElem_map, List.getElem_range]
  have hcol : j < ((List.range p).map fun j =>
      ((List.range n).map fun k =>
        (A.getD i []).getD k 0 * (B.getD k []).getD j 0).sum).length := by
    simpa using hj
  rw [List.getD_eq_getElem (l := (List.range p).map fun j =>
      ((List.range n).map fun k =>
        (A.getD i []).getD k 0 * (B.getD k []).getD j 0).sum)
      (d := 0) hcol]
  simp only [List.getElem_map, List.getElem_range, beq_self_eq_true]

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

lemma rowsToMatrix_mul_matrix_mul_eq_of_mulEqB {m n}
    {A₀ : Matrix (Fin m) (Fin n) ℤ}
    {U A UA V D : List (List Int)}
    (hA : A₀ = rowsToMatrix A m n)
    (hUA : mulEqB U A UA m m n = true)
    (hUAV : mulEqB UA V D m n n = true) :
    rowsToMatrix U m m * A₀ * rowsToMatrix V n n = rowsToMatrix D m n := by
  rw [hA, mulEqB_sound hUA, mulEqB_sound hUAV]

end ChainCert.Reflect
