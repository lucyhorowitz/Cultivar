import ChainCert.Boundary.Basis
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Matrix.Mul

variable {ι : Type} [DecidableEq ι]

theorem eraseIdx_eraseIdx_of_le (l : List α) (i j : ℕ) (h : i ≤ j) :
    (l.eraseIdx (j + 1)).eraseIdx i = (l.eraseIdx i).eraseIdx j := by
  induction l generalizing i j with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.eraseIdx_cons_succ]
        exact congrArg (a :: ·) (ih i j (by omega))

theorem eraseIdx_eraseIdx_of_lt (l : List α) (i j : ℕ) (h : i < j) :
      (l.eraseIdx j).eraseIdx i = (l.eraseIdx i).eraseIdx (j - 1) := by
  obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simpa using eraseIdx_eraseIdx_of_le l i j (by omega)

/- Makes deletionIndex deterministic -/
theorem eraseIdx_injOn_of_nodup (l : List α) (hl : l.Nodup) {a b} (ha : a < l.length) :
    l.eraseIdx a = l.eraseIdx b → a = b := by
  intro h
  by_contra!
  have h' : l[a] ∈ l.eraseIdx b := by
    rw [List.mem_eraseIdx_iff_getElem]
    use a; simp_all
  rw [← h, List.mem_eraseIdx_iff_getElem] at h'
  obtain ⟨c, hc, hc1, hc2⟩ := h'
  exact hc1 (hl.getElem_inj_iff.mp hc2)

-- characterize boundaryCoeff:

theorem boundaryCoeff_eraseIdx (σ : List ι) (hσ : σ.Nodup) {a} (ha : a < σ.length) :
    boundaryCoeff σ (σ.eraseIdx a) = signOfIndex a := by
  have hcongr : ∀ i ∈ List.range σ.length,
      decide (σ.eraseIdx i = σ.eraseIdx a) = decide (i = a) := by
    intro i hi
    rw [List.mem_range] at hi
    simp only [decide_eq_decide]
    constructor
    · exact fun a_1 ↦ eraseIdx_injOn_of_nodup σ hσ hi a_1
    · exact fun a_1 ↦
        List.append_cancel_left (congrArg (HAppend.hAppend σ) (congrArg σ.eraseIdx a_1))
  have hmatch : deletionMatches σ (σ.eraseIdx a) = [a] := by
    unfold deletionMatches
    rw [List.filter_congr hcongr, List.filter_eq]
    simp_all
  simp_all
  have hidx : deletionIndex σ (σ.eraseIdx a) = some a := by
    simp only [deletionIndex, hmatch]
  simp only [boundaryCoeff, hidx]

lemma signOfIndex_ne_zero (i : Nat) : signOfIndex i ≠ 0 := by
  unfold signOfIndex
  by_cases h2 : i % 2 = 0 <;> simp_all

theorem boundaryCoeff_eq_zero_iff (σ τ : List ι) (hσ : σ.Nodup) :
    boundaryCoeff σ τ = 0 ↔ ∀ a < σ.length, σ.eraseIdx a ≠ τ := by
  constructor
  · intro h i hi
    by_contra
    rw [← this] at h
    rw [boundaryCoeff_eraseIdx σ hσ hi] at h
    apply signOfIndex_ne_zero at h
    exact h
  · intro h
    have hempty : deletionMatches σ τ = [] := by
      unfold deletionMatches
      simp_all
    have hnone : deletionIndex σ τ = none := by
      simp only [deletionIndex, hempty]
    simp only [boundaryCoeff, hnone]

/-- Consecutive `signOfIndex` values are negatives of each other. -/
lemma signOfIndex_succ (n : ℕ) : signOfIndex (n + 1) = - signOfIndex n := by
  unfold signOfIndex
  by_cases h : n % 2 = 0
  · have : (n + 1) % 2 ≠ 0 := by omega
    simp [h, this]
  · have : (n + 1) % 2 = 0 := by omega
    simp [h, this]

/-- `boundaryCoeff` written as an explicit (single-term-or-zero) sum over deletion
indices, valid for a `Nodup` simplex. This exposes the inner deletion index so that
the chain condition can be proved as a double sum. -/
lemma boundaryCoeff_eq_sum (ρ τ : List ι) (hρ : ρ.Nodup) :
    boundaryCoeff ρ τ
      = ∑ b ∈ Finset.range ρ.length, if ρ.eraseIdx b = τ then signOfIndex b else 0 := by
  by_cases hex : ∃ b ∈ Finset.range ρ.length, ρ.eraseIdx b = τ
  · obtain ⟨b₀, hb₀mem, hb₀eq⟩ := hex
    rw [Finset.mem_range] at hb₀mem
    rw [Finset.sum_eq_single b₀]
    · rw [if_pos hb₀eq, ← hb₀eq, boundaryCoeff_eraseIdx ρ hρ hb₀mem]
    · intro b hb hbne
      rw [Finset.mem_range] at hb
      rw [if_neg]
      intro hc
      exact hbne (eraseIdx_injOn_of_nodup ρ hρ hb (hc.trans hb₀eq.symm))
    · intro hb0
      exact absurd (Finset.mem_range.mpr hb₀mem) hb0
  · push_neg at hex
    have hz : boundaryCoeff ρ τ = 0 :=
      (boundaryCoeff_eq_zero_iff ρ τ hρ).mpr (fun a ha => hex a (Finset.mem_range.mpr ha))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    rw [if_neg (hex b hb)]

/-- The chain condition at the level of coefficients: for a `Nodup` simplex `σ`, the
alternating sum over deletion indices of the iterated boundary coefficient into a
fixed `τ` vanishes. This is the combinatorial heart of `∂ ∘ ∂ = 0`. -/
theorem boundary_sq_coeff (σ τ : List ι) (hσ : σ.Nodup) :
    ∑ a ∈ Finset.range σ.length, signOfIndex a * boundaryCoeff (σ.eraseIdx a) τ = 0 := by
  -- Expand each inner `boundaryCoeff` into a sum over the (length - 1) deletion indices.
  have key : ∀ a ∈ Finset.range σ.length,
      signOfIndex a * boundaryCoeff (σ.eraseIdx a) τ
        = ∑ b ∈ Finset.range (σ.length - 1),
            if (σ.eraseIdx a).eraseIdx b = τ then signOfIndex a * signOfIndex b else 0 := by
    intro a ha
    rw [Finset.mem_range] at ha
    rw [boundaryCoeff_eq_sum _ τ (hσ.eraseIdx a), List.length_eraseIdx_of_lt ha, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_ite, mul_zero]
  rw [Finset.sum_congr rfl key, ← Finset.sum_product']
  -- A sign-reversing involution on pairs of deletion indices cancels the double sum.
  refine Finset.sum_involution
    (fun p _ => if p.2 < p.1 then (p.2, p.1 - 1) else (p.2 + 1, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨ha, hb⟩ := hab
    by_cases hba : b < a
    · simp only [hba, if_pos]
      have hcomm : (σ.eraseIdx a).eraseIdx b = (σ.eraseIdx b).eraseIdx (a - 1) :=
        eraseIdx_eraseIdx_of_lt σ b a hba
      have hsign : signOfIndex (a - 1) = - signOfIndex a := by
        have ha1 : a - 1 + 1 = a := by omega
        have hs := signOfIndex_succ (a - 1)
        rw [ha1] at hs
        linarith
      rw [hcomm]
      by_cases hc : (σ.eraseIdx b).eraseIdx (a - 1) = τ
      · rw [if_pos hc, if_pos hc, hsign]; ring
      · rw [if_neg hc, if_neg hc]; ring
    · simp only [hba, if_neg, not_false_iff]
      have hab' : a < b + 1 := by omega
      have hcomm : (σ.eraseIdx (b + 1)).eraseIdx a = (σ.eraseIdx a).eraseIdx b := by
        have := eraseIdx_eraseIdx_of_lt σ a (b + 1) hab'
        simpa using this
      have hsign : signOfIndex (b + 1) = - signOfIndex b := signOfIndex_succ b
      rw [hcomm]
      by_cases hc : (σ.eraseIdx a).eraseIdx b = τ
      · rw [if_pos hc, if_pos hc, hsign]; ring
      · rw [if_neg hc, if_neg hc]; ring
  · rintro ⟨a, b⟩ _ _
    by_cases hba : b < a
    · simp only [hba, if_pos]; intro hcon; simp only [Prod.mk.injEq] at hcon; omega
    · simp only [hba, if_neg, not_false_iff]; intro hcon; simp only [Prod.mk.injEq] at hcon; omega
  · rintro ⟨a, b⟩ hab
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨ha, hb⟩ := hab
    by_cases hba : b < a
    · simp only [hba, if_pos, Finset.mem_product, Finset.mem_range]
      omega
    · simp only [hba, if_neg, not_false_iff, Finset.mem_product, Finset.mem_range]
      omega
  · rintro ⟨a, b⟩ hab
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨ha, hb⟩ := hab
    by_cases hba : b < a
    · have hba' : ¬ (a - 1 < b) := by omega
      have heq : a - 1 + 1 = a := by omega
      simp only [hba, if_pos, hba', if_neg, not_false_iff, heq]
    · have hba' : a < b + 1 := by omega
      have heq : b + 1 - 1 = b := by omega
      simp only [hba, if_neg, not_false_iff, hba', if_pos, heq]

/-! ## Bridge to the boundary matrix

This section derives `boundaryMatrix F k * boundaryMatrix F (k+1) = 0`
from `boundary_sq_coeff`. The mathematical reindexing is `boundary_basis_sum_eq_zero`;
the `canonicalBasisRaw` facts below are pure encoding bookkeeping. -/

/-- Reindex a basis-indexed iterated-boundary sum to the deletion-index sum killed
by `boundary_sq_coeff`. The nonzero terms are exactly the codimension-one faces
`σ.eraseIdx a` of `σ`; `hclose` says every such face occurs in the basis list `L`,
and `hLnodup` makes the occurrence unique. -/
lemma boundary_basis_sum_eq_zero (L : List (List ι)) (σ τ : List ι)
    (hσ : σ.Nodup) (hLnodup : L.Nodup)
    (hclose : ∀ a, a < σ.length → σ.eraseIdx a ∈ L) :
    ∑ x : Fin L.length, boundaryCoeff (L[x]) τ * boundaryCoeff σ (L[x]) = 0 := by
  let F : List ι → ℤ := fun ρ => boundaryCoeff ρ τ * boundaryCoeff σ ρ
  change ∑ x : Fin L.length, F (L[x]) = 0
  -- Step 1: rewrite the Fin-indexed sum as a sum over the basis as a Finset.
  have h1 : ∑ x : Fin L.length, F (L[x]) = ∑ ρ ∈ L.toFinset, F ρ := by
    rw [List.sum_toFinset F hLnodup, ← List.ofFn_getElem_eq_map L F]
    exact (Fin.sum_ofFn _).symm
  rw [h1]
  -- Step 2: only codimension-one faces of `σ` contribute, so reindex onto `range σ.length`.
  have hinj : ∀ a ∈ Finset.range σ.length, ∀ b ∈ Finset.range σ.length,
      σ.eraseIdx a = σ.eraseIdx b → a = b := by
    intro a ha b _ hab
    rw [Finset.mem_range] at ha
    exact eraseIdx_injOn_of_nodup σ hσ ha hab
  have h2 : ∑ ρ ∈ L.toFinset, F ρ = ∑ a ∈ Finset.range σ.length, F (σ.eraseIdx a) := by
    rw [← Finset.sum_image hinj]
    symm
    apply Finset.sum_subset
    · intro ρ hρ
      rw [Finset.mem_image] at hρ
      obtain ⟨a, ha, rfl⟩ := hρ
      rw [Finset.mem_range] at ha
      exact List.mem_toFinset.mpr (hclose a ha)
    · intro ρ _ hρnot
      have hz : boundaryCoeff σ ρ = 0 := by
        rw [boundaryCoeff_eq_zero_iff σ ρ hσ]
        intro a ha hcontra
        exact hρnot (Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, hcontra⟩)
      change boundaryCoeff ρ τ * boundaryCoeff σ ρ = 0
      rw [hz, mul_zero]
  rw [h2]
  -- Step 3: each surviving term is `signOfIndex a * boundaryCoeff (σ.eraseIdx a) τ`.
  rw [show
        (∑ a ∈ Finset.range σ.length, F (σ.eraseIdx a))
          = ∑ a ∈ Finset.range σ.length,
              signOfIndex a * boundaryCoeff (σ.eraseIdx a) τ from ?_]
  · exact boundary_sq_coeff σ τ hσ
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    change boundaryCoeff (σ.eraseIdx a) τ * boundaryCoeff σ (σ.eraseIdx a)
        = signOfIndex a * boundaryCoeff (σ.eraseIdx a) τ
    rw [boundaryCoeff_eraseIdx σ hσ ha]
    ring

variable [Fintype ι] [LinearOrder ι]

omit [DecidableEq ι] in
lemma mem_encodeVertexOrder (v : ι) : v ∈ encodeVertexOrder (ι := ι) := by
  rw [encodeVertexOrder, Finset.mem_sort]
  exact Finset.mem_univ v

omit [DecidableEq ι] in
lemma encodeVertexOrder_nodup : (encodeVertexOrder (ι := ι)).Nodup := by
  rw [encodeVertexOrder]; exact Finset.sort_nodup _ _

lemma encodeVertexOrder_idxOf_injective :
    Function.Injective (fun v : ι => encodeVertexOrder.idxOf v) := by
  intro x y h
  exact (List.idxOf_inj (mem_encodeVertexOrder x)).mp h

lemma encodeSimplex_injective : Function.Injective (encodeSimplex (ι := ι)) :=
  List.map_injective_iff.mpr encodeVertexOrder_idxOf_injective

/-- The canonical basis enumeration has no repeated simplices. -/
lemma canonicalBasisRaw_nodup (F : FiniteFacetComplex ι) (k : ℕ) :
    (canonicalBasisRaw F k).Nodup := by
  simp only [canonicalBasisRaw]
  rw [(List.mergeSort_perm _ _).nodup_iff]
  exact
    (List.nodup_sublistsLen _ encodeVertexOrder_nodup).filter _ |>.map
      encodeSimplex_injective

/-- Every simplex in the canonical basis is itself duplicate-free. -/
lemma basis_entry_nodup (F : FiniteFacetComplex ι) (k : ℕ) {σ : List Nat}
    (h : σ ∈ canonicalBasisRaw F k) : σ.Nodup := by
  simp only [canonicalBasisRaw, List.mem_mergeSort, List.mem_map, List.mem_filter] at h
  obtain ⟨τ, ⟨hτcand, _⟩, rfl⟩ := h
  rw [List.mem_sublistsLen] at hτcand
  exact List.Nodup.map encodeVertexOrder_idxOf_injective
    (hτcand.1.nodup encodeVertexOrder_nodup)

/-- Deleting a vertex from a basis `(m+1)`-simplex yields a basis `m`-simplex:
the canonical basis is closed under taking codimension-one faces. -/
lemma basis_eraseIdx_closed (F : FiniteFacetComplex ι) (m : ℕ) {σ : List Nat}
    (h : σ ∈ canonicalBasisRaw F (m + 1)) (a : ℕ) (ha : a < σ.length) :
    σ.eraseIdx a ∈ canonicalBasisRaw F m := by
  simp only [canonicalBasisRaw, List.mem_mergeSort, List.mem_map, List.mem_filter] at h ⊢
  obtain ⟨τ, ⟨hτcand, hτface⟩, rfl⟩ := h
  rw [List.mem_sublistsLen] at hτcand
  obtain ⟨hτsub, hτlen⟩ := hτcand
  -- `a` indexes into `encodeSimplex τ`, hence into `τ`
  simp only [encodeSimplex, List.length_map] at ha
  have hτnodup : τ.Nodup := hτsub.nodup encodeVertexOrder_nodup
  have heraseSub : (τ.eraseIdx a).Sublist encodeVertexOrder :=
    (List.eraseIdx_sublist τ a).trans hτsub
  have heraseNodup : (τ.eraseIdx a).Nodup := heraseSub.nodup encodeVertexOrder_nodup
  have heraseLen : (τ.eraseIdx a).length = m + 1 := by
    rw [List.length_eraseIdx_of_lt ha, hτlen]
    omega
  refine ⟨τ.eraseIdx a, ⟨?_, ?_⟩, ?_⟩
  · rw [List.mem_sublistsLen]
    exact ⟨heraseSub, heraseLen⟩
  · rw [decide_eq_true_eq] at hτface ⊢
    obtain ⟨_, f, hf, hsub⟩ := hτface
    refine ⟨?_, f, hf, ?_⟩
    · rw [List.toFinset_card_of_nodup heraseNodup, heraseLen]
    · refine subset_trans ?_ hsub
      intro x hx
      exact List.mem_toFinset.mpr
        ((List.eraseIdx_sublist τ a).subset (List.mem_toFinset.mp hx))
  · simp only [encodeSimplex]
    exact (List.eraseIdx_map _ τ a).symm

/-- The chain condition for the certified boundary matrices: consecutive simplicial
boundary maps compose to zero. -/
theorem boundaryMatrix_comp_eq_zero (F : FiniteFacetComplex ι) (k : ℕ) :
    boundaryMatrix F k * boundaryMatrix F (k + 1) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [boundaryMatrix, Matrix.of_apply, Matrix.zero_apply]
  exact boundary_basis_sum_eq_zero
    (canonicalBasisRaw F (k + 1))
    ((canonicalBasisRaw F (k + 2))[j.val]'j.isLt)
    ((canonicalBasisRaw F k)[i.val]'i.isLt)
    (basis_entry_nodup F (k + 2) (List.getElem_mem _))
    (canonicalBasisRaw_nodup F (k + 1))
    (fun a ha => basis_eraseIdx_closed F (k + 1) (List.getElem_mem _) a ha)
