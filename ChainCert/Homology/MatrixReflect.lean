import ChainCert.Homology.Basic
import ChainCert.MatrixReflect

namespace ChainCert.Reflect

open ChainCert.SageDecode

def dropRows (r : Nat) (A : List (List Int)) : List (List Int) :=
  A.drop r

def cyclePresentationRowsB
    (VinvRows dk1Rows MRows : List (List Int)) (r n p : Nat) : Bool :=
  rowsEqB (dropRows r (mulRows VinvRows dk1Rows n n p)) MRows (n - r) p

lemma getD_drop {α : Type} (Rows : List α) (r i : Nat) (d : α) :
    (Rows.drop r).getD i d = Rows.getD (r + i) d := by
  by_cases h : i < (Rows.drop r).length
  · rw [List.getD_eq_getElem (l := Rows.drop r) (d := d) h]
    have hri : r + i < Rows.length := by
      have h' := h
      simp [List.length_drop] at h'
      omega
    rw [List.getD_eq_getElem (l := Rows) (d := d) hri]
    simp [List.getElem_drop]
  · rw [List.getD_eq_default (l := Rows.drop r) (d := d) (Nat.le_of_not_gt h)]
    have hri : Rows.length ≤ r + i := by
      have h' : (Rows.drop r).length ≤ i := Nat.le_of_not_gt h
      simp [List.length_drop] at h'
      omega
    rw [List.getD_eq_default (l := Rows) (d := d) hri]

lemma bottomRows_rowsToMatrix_eq_dropRows {n p r : Nat}
    (hr : r ≤ n) (Rows : List (List Int)) :
    bottomRows r (rowsToMatrix Rows n p) =
      rowsToMatrix (dropRows r Rows) (n - r) p := by
  ext i j
  unfold bottomRows rowsToMatrix dropRows
  rw [bottomRowIndex_val_of_le hr]
  rw [← getD_drop]

lemma rowsToMatrix_eq_cyclePresentationMatrix_of_cyclePresentationRowsB
    {n p : Nat}
    {dk1 : Matrix (Fin n) (Fin p) ℤ}
    {VinvRows dk1Rows MRows : List (List Int)}
    {r : Nat}
    (hr : r ≤ n)
    (hdk1 : dk1 = rowsToMatrix dk1Rows n p)
    (hcheck :
      cyclePresentationRowsB VinvRows dk1Rows MRows r n p = true) :
    ChainCert.SageDecode.rowsToMatrix MRows (n - r) p =
      bottomRows r (ChainCert.SageDecode.rowsToMatrix VinvRows n n * dk1) := by
  rw [hdk1]
  rw [mulEqB_sound (mulRows_mulEqB VinvRows dk1Rows n n p)]
  rw [bottomRows_rowsToMatrix_eq_dropRows hr]
  exact (rowsEqB_sound hcheck).symm

end ChainCert.Reflect
