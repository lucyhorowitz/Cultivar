import ChainCert.Homology.Basic
import ChainCert.SNF.Bridge
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Bridges from homology certificates to Mathlib linear algebra

This file defines the ordinary algebraic quotient represented by a pair of
boundary matrices,

```lean
ker dₖ / im dₖ₊₁,
```

and records the first bridge theorem: the chain condition stored in a
`ChainQuotientCert` is exactly what makes `im dₖ₊₁` a submodule of `ker dₖ`.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
                     [DecidableEq R] [SageSerializable R]
variable {m n p : ℕ}

open scoped Matrix

/-- The cycle submodule of a matrix boundary map. -/
abbrev cycles (dk : Matrix (Fin m) (Fin n) R) : Submodule R (Fin n → R) :=
  LinearMap.ker (matLin dk)

omit [IsDomain R] [IsPrincipalIdealRing R] [DecidableEq R] [SageSerializable R] in
/-- If consecutive matrix boundary maps compose to zero, then the image of the
second lies in the kernel of the first. -/
theorem matRange_le_cycles_of_comp_eq_zero
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (hCC : dk * dk1 = 0) :
    matRange dk1 ≤ cycles dk := by
  rintro y ⟨z, hz⟩
  rw [cycles, LinearMap.mem_ker, matLin, Matrix.mulVecLin_apply]
  rw [← hz]
  calc
    dk *ᵥ (dk1 *ᵥ z) = (dk * dk1) *ᵥ z := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hCC, Matrix.zero_mulVec]

/-- The boundary image, regarded as a submodule of cycles. -/
def boundaryImageInCycles
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R)
    (hCC : dk * dk1 = 0) :
    Submodule R (cycles dk) :=
  (matRange dk1).comap (cycles dk).subtype

/-- The ordinary algebraic homology module represented by two consecutive
boundary matrices. -/
def matrixHomology
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R)
    (hCC : dk * dk1 = 0) : Type _ :=
  cycles dk ⧸ boundaryImageInCycles dk dk1 hCC

instance matrixHomology.instAddCommGroup
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R)
    (hCC : dk * dk1 = 0) :
    AddCommGroup (matrixHomology dk dk1 hCC) := by
  dsimp [matrixHomology]
  exact Submodule.Quotient.addCommGroup (boundaryImageInCycles dk dk1 hCC)

instance matrixHomology.instModule
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R)
    (hCC : dk * dk1 = 0) :
    Module R (matrixHomology dk dk1 hCC) := by
  dsimp [matrixHomology]
  exact Submodule.Quotient.module (boundaryImageInCycles dk dk1 hCC)

namespace CertificateSNF

omit [IsDomain R] [IsPrincipalIdealRing R] [SageSerializable R] [DecidableEq R] in
theorem diagonal_row_mulVec_eq
    {D : Matrix (Fin m) (Fin n) R} (hdiag : IsDiagonal D)
    {i : Fin m} {j : Fin n} (hij : i.val = j.val) (x : Fin n → R) :
    (D *ᵥ x) i = D i j * x j := by
  rw [Matrix.mulVec]
  unfold dotProduct
  refine Finset.sum_eq_single j ?_ ?_
  · intro b _ hb
    have hne : i.val ≠ b.val := by
      intro h
      apply hb
      ext
      omega
    simp [hdiag i b hne]
  · intro hmem
    exact (hmem (Finset.mem_univ j)).elim

theorem diagonal_mulVec_extendBottomCoordinates_eq_zero
    {dk : Matrix (Fin m) (Fin n) R}
    (certK : CertificateSNF (A := dk)) (x : Fin (n - certK.r) → R) :
    certK.D *ᵥ extendBottomCoordinates (R := R) certK.r n x = 0 := by
  classical
  ext i
  rw [Matrix.mulVec]
  unfold dotProduct
  refine Finset.sum_eq_zero ?_
  intro j _
  by_cases hij : i.val = j.val
  · by_cases hlt : i.val < certK.r
    · have hjlt : j.val < certK.r := by omega
      simp [extendBottomCoordinates_apply_of_lt (R := R) x hjlt]
    · have hmin : i.val < min m n := by
        have : i.val < m := i.isLt
        have : j.val < n := j.isLt
        omega
      let q : Fin (min m n) := ⟨i.val, hmin⟩
      have hdiag_zero : diagEntry certK.D q = 0 := by
        exact (certK.hrank q).2 (by
          change certK.r ≤ i.val
          exact Nat.le_of_not_gt hlt)
      have hD : certK.D i j = diagEntry certK.D q := by
        unfold diagEntry
        congr <;> ext <;> simp [q, hij]
      simp [hD, hdiag_zero]
  · have hD : certK.D i j = 0 := certK.hdiag i j hij
    simp [hD]

omit [IsDomain R] [IsPrincipalIdealRing R] [SageSerializable R] in
theorem diagonal_mulVec_vinv_eq_zero_of_mem_cycles
    {dk : Matrix (Fin m) (Fin n) R}
    (certK : CertificateSNF (A := dk)) (x : cycles dk) :
    certK.D *ᵥ (certK.Vinv *ᵥ (x : Fin n → R)) = 0 := by
  have hx : dk *ᵥ (x : Fin n → R) = 0 := by
    have hx' : matLin dk (x : Fin n → R) = 0 := x.property
    exact hx'
  calc
    certK.D *ᵥ (certK.Vinv *ᵥ (x : Fin n → R))
        = (certK.U * dk * certK.V) *ᵥ (certK.Vinv *ᵥ (x : Fin n → R)) := by
            rw [certK.heq]
    _ = certK.U *ᵥ (dk *ᵥ (x : Fin n → R)) := by
      rw [Matrix.mulVec_mulVec]
      calc
        (certK.U * dk * certK.V * certK.Vinv) *ᵥ (x : Fin n → R)
            = ((certK.U * dk) * (certK.V * certK.Vinv)) *ᵥ
                (x : Fin n → R) := by
                rw [Matrix.mul_assoc]
        _ = ((certK.U * dk) * (1 : Matrix (Fin n) (Fin n) R)) *ᵥ
                (x : Fin n → R) := by
                rw [certK.hVVinv]
        _ = (certK.U * dk) *ᵥ (x : Fin n → R) := by rw [Matrix.mul_one]
        _ = certK.U *ᵥ (dk *ᵥ (x : Fin n → R)) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by simp [hx]

omit [IsPrincipalIdealRing R] [SageSerializable R] in
theorem vinv_mulVec_eq_zero_of_mem_cycles_of_lt
    {dk : Matrix (Fin m) (Fin n) R}
    (certK : CertificateSNF (A := dk)) (x : cycles dk)
    {j : Fin n} (hj : j.val < certK.r) :
    (certK.Vinv *ᵥ (x : Fin n → R)) j = 0 := by
  classical
  have hrmin : certK.r ≤ min m n := certK.rankCutoff_le_min
  let i : Fin m := ⟨j.val, by omega⟩
  have hDzero := congr_fun
    (diagonal_mulVec_vinv_eq_zero_of_mem_cycles (R := R) certK x) i
  have hrow :
      certK.D i j * (certK.Vinv *ᵥ (x : Fin n → R)) j = 0 := by
    rwa [diagonal_row_mulVec_eq (R := R) certK.hdiag (i := i) (j := j) (by simp [i])]
      at hDzero
  have hmin : j.val < min m n := by omega
  let q : Fin (min m n) := ⟨j.val, hmin⟩
  have hdiag_ne : certK.D i j ≠ 0 := by
    have hentry_ne : diagEntry certK.D q ≠ 0 := by
      intro hzero
      have hle : certK.r ≤ q.val := (certK.hrank q).1 hzero
      have : certK.r ≤ j.val := by
        simpa [q] using hle
      omega
    have hD : certK.D i j = diagEntry certK.D q := by
      unfold diagEntry
      congr
    simpa [hD] using hentry_ne
  exact (eq_zero_or_eq_zero_of_mul_eq_zero hrow).resolve_left hdiag_ne

theorem vk_extendBottom_mem_cycles
    {dk : Matrix (Fin m) (Fin n) R}
    (certK : CertificateSNF (A := dk)) (x : Fin (n - certK.r) → R) :
    certK.V *ᵥ extendBottomCoordinates (R := R) certK.r n x ∈ cycles dk := by
  have hD :
      certK.D *ᵥ extendBottomCoordinates (R := R) certK.r n x = 0 :=
    diagonal_mulVec_extendBottomCoordinates_eq_zero (R := R) certK x
  rw [cycles, LinearMap.mem_ker, matLin, Matrix.mulVecLin_apply]
  have hU :
      certK.U *ᵥ
          (dk *ᵥ (certK.V *ᵥ extendBottomCoordinates (R := R) certK.r n x)) = 0 := by
    calc
      certK.U *ᵥ
          (dk *ᵥ (certK.V *ᵥ extendBottomCoordinates (R := R) certK.r n x))
          = (certK.U * dk * certK.V) *ᵥ
              extendBottomCoordinates (R := R) certK.r n x := by
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = certK.D *ᵥ extendBottomCoordinates (R := R) certK.r n x := by
              rw [certK.heq]
      _ = 0 := hD
  let z : Fin m → R :=
    dk *ᵥ (certK.V *ᵥ extendBottomCoordinates (R := R) certK.r n x)
  have hU' : certK.Uinv *ᵥ (certK.U *ᵥ z) = 0 := by
    rw [show certK.U *ᵥ z = 0 by simpa [z] using hU]
    simp
  have hU'' : (certK.Uinv * certK.U) *ᵥ z = 0 := by
    simpa [Matrix.mulVec_mulVec] using hU'
  rw [certK.hUinvU, Matrix.one_mulVec] at hU''
  simpa [z] using hU''

/-- The coordinate equivalence on cycles induced by an SNF certificate for
`dk`.

Mathematically, this applies the certified inverse column change `Vinv` and then
keeps the bottom coordinates, i.e. the coordinates after the rank cutoff
`certK.r`.  The statement is packaged as a linear equivalence because the SNF
certificate for `dk` should identify `ker dk` with a free module on those bottom
coordinates. -/
noncomputable def cycleCoordinateEquiv
    {dk : Matrix (Fin m) (Fin n) R}
    (certK : CertificateSNF (A := dk)) :
    cycles dk ≃ₗ[R] (Fin (n - certK.r) → R) := by
  classical
  refine
    { toFun := fun x =>
        bottomCoordinates (R := R) certK.r n
          (certK.Vinv *ᵥ (x : Fin n → R))
      invFun := fun x =>
        ⟨certK.V *ᵥ extendBottomCoordinates (R := R) certK.r n x,
          vk_extendBottom_mem_cycles (R := R) certK x⟩
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro x y
    ext i
    simp [bottomCoordinates, Matrix.mulVec_add]
  · intro a x
    ext i
    simp only [bottomCoordinates, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec,
      dotProduct, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    change (∑ x_1, certK.Vinv (bottomRowIndex certK.r n i) x_1 *
        (a * (x : Fin n → R) x_1)) =
      a * ∑ x_1, certK.Vinv (bottomRowIndex certK.r n i) x_1 * (x : Fin n → R) x_1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  · intro x
    ext j
    have hrn : certK.r ≤ n := by
      have := certK.rankCutoff_le_min
      omega
    calc
      (certK.V *ᵥ
          extendBottomCoordinates (R := R) certK.r n
            (bottomCoordinates (R := R) certK.r n
              (certK.Vinv *ᵥ (x : Fin n → R)))) j
          = (certK.V *ᵥ (certK.Vinv *ᵥ (x : Fin n → R))) j := by
            congr 1
            exact extendBottomCoordinates_bottomCoordinates_of_eq_zero
              (R := R) hrn (certK.Vinv *ᵥ (x : Fin n → R))
              (fun k hk => vinv_mulVec_eq_zero_of_mem_cycles_of_lt
                (R := R) certK x hk)
      _ = ((certK.V * certK.Vinv) *ᵥ (x : Fin n → R)) j := by
            rw [Matrix.mulVec_mulVec]
      _ = (x : Fin n → R) j := by
            rw [certK.hVVinv, Matrix.one_mulVec]
  · intro x
    have hrn : certK.r ≤ n := by
      have := certK.rankCutoff_le_min
      omega
    calc
      bottomCoordinates (R := R) certK.r n
          (certK.Vinv *ᵥ
            ((certK.V *ᵥ extendBottomCoordinates (R := R) certK.r n x))) =
          bottomCoordinates (R := R) certK.r n
            (((certK.Vinv * certK.V) *ᵥ
              extendBottomCoordinates (R := R) certK.r n x)) := by
            rw [Matrix.mulVec_mulVec]
      _ = bottomCoordinates (R := R) certK.r n
            (extendBottomCoordinates (R := R) certK.r n x) := by
            rw [certK.hVinvV, Matrix.one_mulVec]
      _ = x := bottomCoordinates_extendBottomCoordinates (R := R) hrn x

end CertificateSNF

omit [IsDomain R] [IsPrincipalIdealRing R] [SageSerializable R] [DecidableEq R] in
theorem bottomCoordinates_mulVec_eq_bottomRows_mulVec
    (r : ℕ) (A : Matrix (Fin n) (Fin p) R) (x : Fin p → R) :
    bottomCoordinates (R := R) r n (A *ᵥ x) = bottomRows r A *ᵥ x := by
  ext i
  simp [bottomCoordinates, bottomRows, Matrix.mulVec]

namespace ChainQuotientCert

/-- A chain quotient certificate proves that the certified boundary image is
inside the certified cycles. -/
theorem boundaryImage_le_cycles
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    matRange dk1 ≤ cycles dk :=
  matRange_le_cycles_of_comp_eq_zero cert.hCC

/-- The actual algebraic homology quotient associated to a chain quotient
certificate. -/
abbrev homologyModule
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) : Type _ :=
  matrixHomology dk dk1 cert.hCC

/-- The SNF certificate for the presentation matrix gives a Mathlib quotient
equivalence from that presentation to its diagonal Smith form. -/
noncomputable def presentationCokernelEquivDiagonal
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    ((Fin (n - cert.certK.r) → R) ⧸ matRange cert.M) ≃ₗ[R]
      ((Fin (n - cert.certK.r) → R) ⧸ matRange cert.certM.D) :=
  CertificateSNF.cokernelEquivDiagonal (A := cert.M) cert.certM

/-- Under the cycle-coordinate equivalence coming from the SNF certificate for
`dk`, the boundary image `im dk1` inside `ker dk` is exactly the range of the
stored presentation matrix `M`.

This is the central bookkeeping lemma behind the homology bridge.  It says that
the matrix `M` stored in the certificate is not merely some auxiliary matrix: it
is precisely the boundary image expressed in the certified coordinates on
cycles. -/
theorem map_boundaryImage_eq_presentationRange
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    (boundaryImageInCycles dk dk1 cert.hCC).map
        (CertificateSNF.cycleCoordinateEquiv (R := R) (m := m) (n := n)
          (dk := dk) cert.certK :
          cycles dk →ₗ[R] (Fin (n - cert.certK.r) → R)) =
      matRange cert.M := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    change (x : Fin n → R) ∈ matRange dk1 at hx
    rcases hx with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← hxy]
    rw [matLin, Matrix.mulVecLin_apply]
    symm
    change
      bottomCoordinates (R := R) cert.certK.r n
        (cert.certK.Vinv *ᵥ (x : Fin n → R)) = cert.M *ᵥ z
    rw [← hz]
    calc
      bottomCoordinates (R := R) cert.certK.r n
          (cert.certK.Vinv *ᵥ (dk1 *ᵥ z))
          = bottomCoordinates (R := R) cert.certK.r n
              ((cert.certK.Vinv * dk1) *ᵥ z) := by
              rw [Matrix.mulVec_mulVec]
      _ = bottomRows cert.certK.r (cert.certK.Vinv * dk1) *ᵥ z := by
              rw [bottomCoordinates_mulVec_eq_bottomRows_mulVec]
      _ = cyclePresentationMatrix cert.certK dk1 *ᵥ z := by
              rfl
      _ = cert.M *ᵥ z := by
              rw [cert.hM]
  · rintro ⟨z, hz⟩
    let x : cycles dk :=
      ⟨dk1 *ᵥ z, by
        rw [cycles, LinearMap.mem_ker, matLin, Matrix.mulVecLin_apply]
        calc
          dk *ᵥ (dk1 *ᵥ z) = (dk * dk1) *ᵥ z := by
              rw [Matrix.mulVec_mulVec]
          _ = 0 := by rw [cert.hCC, Matrix.zero_mulVec]⟩
    refine ⟨x, ?_, ?_⟩
    · change (x : Fin n → R) ∈ matRange dk1
      exact ⟨z, by rw [matLin, Matrix.mulVecLin_apply]⟩
    · rw [← hz]
      change
        bottomCoordinates (R := R) cert.certK.r n
          (cert.certK.Vinv *ᵥ (x : Fin n → R)) = cert.M *ᵥ z
      calc
        bottomCoordinates (R := R) cert.certK.r n
            (cert.certK.Vinv *ᵥ (x : Fin n → R))
            = bottomCoordinates (R := R) cert.certK.r n
                (cert.certK.Vinv *ᵥ (dk1 *ᵥ z)) := by
                rfl
        _ = bottomCoordinates (R := R) cert.certK.r n
              ((cert.certK.Vinv * dk1) *ᵥ z) := by
              rw [Matrix.mulVec_mulVec]
        _ = bottomRows cert.certK.r (cert.certK.Vinv * dk1) *ᵥ z := by
              rw [bottomCoordinates_mulVec_eq_bottomRows_mulVec]
        _ = cyclePresentationMatrix cert.certK dk1 *ᵥ z := by
              rfl
        _ = cert.M *ᵥ z := by
              rw [cert.hM]

/-- A chain quotient certificate identifies the actual algebraic homology
quotient

`ker dk / im dk1`

with the cokernel of the stored presentation matrix `M`.

This is the main theorem needed to justify the `homology` certificate format:
after this theorem, the rest of the computation is ordinary Smith normal form
on `M`. -/
noncomputable def homologyEquivPresentation
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    cert.homologyModule ≃ₗ[R]
      ((Fin (n - cert.certK.r) → R) ⧸ matRange cert.M) :=
  Submodule.Quotient.equiv
    (boundaryImageInCycles dk dk1 cert.hCC)
    (matRange cert.M)
    (CertificateSNF.cycleCoordinateEquiv (R := R) (m := m) (n := n)
      (dk := dk) cert.certK)
    (map_boundaryImage_eq_presentationRange (R := R) cert)

/-- Combining `homologyEquivPresentation` with the existing SNF bridge for `M`
identifies the homology quotient with the cokernel of the certified diagonal
Smith form of `M`.

This is the matrix-level version of the final correctness theorem for a
homology certificate. -/
noncomputable def homologyEquivDiagonal
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    cert.homologyModule ≃ₗ[R]
      ((Fin (n - cert.certK.r) → R) ⧸ matRange cert.certM.D) :=
  (homologyEquivPresentation (R := R) cert).trans
    (presentationCokernelEquivDiagonal (R := R) cert)

/-- Combine `homologyEquivDiagonal` with `diagonalCokernelPiEquiv` to identify
the homology quotient with a product of ideal quotients, one per row of the
certified diagonal Smith form `D` of the presentation matrix.

For `R = ℤ`, each factor is either `ℤ` (when the corresponding diagonal entry
is `0`, including all rows beyond the rank), `0` (when the entry is a unit), or
`ℤ/dℤ` (when the entry is `d`). -/
noncomputable def homologyEquivPi
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    cert.homologyModule ≃ₗ[R]
      ∀ i : Fin (n - cert.certK.r), R ⧸ rowDiagIdeal (R := R) cert.certM.D i :=
  (homologyEquivDiagonal (R := R) cert).trans
    (diagonalCokernelPiEquiv (R := R) cert.certM.hdiag)

end ChainQuotientCert

namespace CertificateHomology

variable {ι : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι]

/-- A homology certificate proves that the next boundary image lies in the
current boundary kernel. -/
theorem boundaryImage_le_cycles {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    matRange (boundaryK (R := R) X (k + 1)) ≤
      cycles (boundaryK (R := R) X k) :=
  cert.quotientCert.boundaryImage_le_cycles

/-- The actual algebraic homology quotient associated to a homology
certificate. -/
abbrev homologyModule {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) : Type _ :=
  cert.quotientCert.homologyModule

/-- The row index type for the certified diagonal homology presentation. -/
abbrev certifiedHomologyIndex {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) : Type :=
  Fin (cellCount X k - cert.quotientCert.certK.r)

/-- The diagonal entry of the certified homology presentation at an index.

For `R = ℤ`, these are the invariant factors returned by the certificate up to
the usual unit ambiguity. -/
def certifiedHomologyDiagonal {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k)
    (i : cert.certifiedHomologyIndex) : R :=
  rowDiagVal (R := R) cert.presentationCert.D i

/-- The ideal generated by one certified homology diagonal entry. -/
abbrev certifiedHomologyIdeal {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k)
    (i : cert.certifiedHomologyIndex) : Submodule R R :=
  rowDiagIdeal (R := R) cert.presentationCert.D i

omit [IsDomain R] [IsPrincipalIdealRing R] [SageSerializable R] in
/-- If a certified diagonal entry is a unit, its quotient factor is trivial. -/
theorem certifiedHomologyIdeal_eq_top_of_isUnit {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k)
    (i : cert.certifiedHomologyIndex)
    (h : IsUnit (cert.certifiedHomologyDiagonal i)) :
    cert.certifiedHomologyIdeal i = ⊤ := by
  change (Ideal.span {cert.certifiedHomologyDiagonal i} : Ideal R) = ⊤
  rw [Ideal.span_singleton_eq_top]
  exact h

omit [IsDomain R] [IsPrincipalIdealRing R] [SageSerializable R] in
/-- If a certified diagonal entry is a unit, the corresponding product factor
in `certifiedHomologyGroup` is a subsingleton. -/
theorem certifiedHomologyFactor_subsingleton_of_isUnit {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k)
    (i : cert.certifiedHomologyIndex)
    (h : IsUnit (cert.certifiedHomologyDiagonal i)) :
    Subsingleton (R ⧸ cert.certifiedHomologyIdeal i) := by
  refine Submodule.Quotient.subsingleton_iff.mpr ?_
  exact cert.certifiedHomologyIdeal_eq_top_of_isUnit i h

/-- The group read directly from a homology certificate.

This is the user-facing target: a product of cyclic/quotient factors indexed by
the certified diagonal Smith form. For `R = ℤ`, each factor is `ℤ`, `0`, or
`ℤ / dℤ` depending on the corresponding diagonal entry. -/
abbrev certifiedHomologyGroup {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) : Type _ :=
  ∀ i : cert.certifiedHomologyIndex, R ⧸ cert.certifiedHomologyIdeal i

/-- The certified presentation of homology has a Mathlib quotient equivalence
to its diagonal Smith form. -/
noncomputable def presentationCokernelEquivDiagonal {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    ((Fin (cellCount X k - cert.quotientCert.certK.r) → R) ⧸
        matRange cert.presentationMatrix) ≃ₗ[R]
      ((Fin (cellCount X k - cert.quotientCert.certK.r) → R) ⧸
        matRange cert.presentationCert.D) :=
  CertificateSNF.cokernelEquivDiagonal (A := cert.presentationMatrix)
    cert.presentationCert

/-- A homology certificate identifies the actual homology quotient of the
boundary maps of `X` in degree `k` with the cokernel of its stored presentation
matrix.

This is the simplicial-complex wrapper around
`ChainQuotientCert.homologyEquivPresentation`. -/
noncomputable def homologyEquivPresentation {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    cert.homologyModule ≃ₗ[R]
      ((Fin (cellCount X k - cert.quotientCert.certK.r) → R) ⧸
        matRange cert.presentationMatrix) :=
  ChainQuotientCert.homologyEquivPresentation (R := R) cert.quotientCert

/-- Final intended correctness statement for `CertificateHomology`: the actual
homology quotient of `X` in degree `k` is linearly equivalent to the cokernel of
the certified diagonal Smith form of the presentation matrix.

For coefficients in `ℤ`, this is the point from which one reads off Betti
numbers and torsion coefficients from the diagonal entries. -/
noncomputable def homologyEquivDiagonal {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    cert.homologyModule ≃ₗ[R]
      ((Fin (cellCount X k - cert.quotientCert.certK.r) → R) ⧸
        matRange cert.presentationCert.D) :=
  (homologyEquivPresentation (R := R) cert).trans
    (presentationCokernelEquivDiagonal (R := R) cert)

/-- A homology certificate identifies the actual homology quotient with the
product of ideal quotients determined by the certified diagonal Smith form of
the presentation matrix. -/
noncomputable def homologyEquivPi {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    cert.homologyModule ≃ₗ[R]
      ∀ i : Fin (cellCount X k - cert.quotientCert.certK.r),
        R ⧸ rowDiagIdeal (R := R) cert.presentationCert.D i :=
  ChainQuotientCert.homologyEquivPi (R := R) cert.quotientCert

/-- One-line correctness theorem for a homology certificate.

The left side is the matrix homology of the simplicial boundary maps of `X` in
degree `k`; the right side is the group that can be read directly from the
certified Smith diagonal. The longer bridge lemmas above are only the
implementation of this statement. -/
noncomputable def correct {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    cert.homologyModule ≃ₗ[R] cert.certifiedHomologyGroup :=
  cert.homologyEquivPi

/-- Proposition-valued wrapper for `correct`, convenient when an example only
needs to state existence of the certified equivalence. -/
theorem homology_is_certified_group {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    Nonempty (cert.homologyModule ≃ₗ[R] cert.certifiedHomologyGroup) :=
  ⟨cert.correct⟩

end CertificateHomology
