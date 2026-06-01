import ChainCert.Examples.Complexes
import ChainCert.Boundary.Verify
import ChainCert.SNF.Tactic
import ChainCert.Homology.Tactic
import ChainCert.Homology.Command
import ChainCert.Homology.Bridge

/-! ## Worked example: `H₁(triangle; ℤ) = 0`

The filled 2-simplex has `H₁ = 0`. The pipeline used here:

* `homology triangleFFC, 1` builds `hTri : CertificateHomology ℤ triangleFFC 1`
  from a Sage-checked SNF;
* `CertificateHomology.correct` identifies the abstract homology quotient with
  the certified group read from the diagonal Smith form returned by Sage;
* on the triangle the presentation matrix has SNF `diag(1)`, so every factor
  is `ℤ ⧸ ⟨1⟩ = 0` and the product is the trivial module. -/

/-- The H₁ certificate for the triangle, produced by the `homology` pipeline
from a Sage-checked SNF. -/
noncomputable def triangleH1Cert : CertificateHomology (R := ℤ) triangleFFC 1 := by
  homology triangleFFC, 1

/-- The certified H₁ of the triangle is the group read from the certificate. -/
theorem triangleH1_correct :
    Nonempty (triangleH1Cert.homologyModule ≃ₗ[ℤ]
      triangleH1Cert.certifiedHomologyGroup) :=
  triangleH1Cert.homology_is_certified_group

/-- `H₁(triangle; ℤ) = 0`: the certified homology module is trivial. -/
theorem triangleH1_subsingleton : Subsingleton triangleH1Cert.homologyModule := by
  haveI : ∀ i : triangleH1Cert.certifiedHomologyIndex,
      Subsingleton (ℤ ⧸ triangleH1Cert.certifiedHomologyIdeal i) := by
    intro i
    exact triangleH1Cert.certifiedHomologyFactor_subsingleton_of_isUnit i (by
      rw [Int.isUnit_iff]
      revert i
      unfold triangleH1Cert
      native_decide)
  exact triangleH1Cert.correct.toEquiv.subsingleton
