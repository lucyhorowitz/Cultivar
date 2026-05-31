import ChainCert.Boundary.Basis
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

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

theorem boundaryCoeff_eraseIdx (σ : List Int) (hσ : σ.Nodup) {a} (ha : a < σ.length) :
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

theorem boundaryCoeff_eq_zero_iff (σ τ : List Int) (hσ : σ.Nodup) :
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
lemma boundaryCoeff_eq_sum (ρ τ : List Int) (hρ : ρ.Nodup) :
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
theorem boundary_sq_coeff (σ τ : List Int) (hσ : σ.Nodup) :
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
