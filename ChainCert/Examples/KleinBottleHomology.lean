import ChainCert.Examples.Complexes
import ChainCert.Boundary.Verify
import ChainCert.SNF.Tactic
import ChainCert.Homology.Tactic
import ChainCert.Homology.Command
import ChainCert.Homology.Bridge

/-!
# `H₁(Klein bottle; ℤ)` certificate

Sage-checked `CertificateHomology` for the Klein bottle over `ℤ`, built from
the minimal 3×3 triangulation `kleinBottleFFC` (18 triangles, 27 edges,
9 vertices).

Target homology (for reference):
* `H₀(Klein; ℤ) ≅ ℤ`
* `H₁(Klein; ℤ) ≅ ℤ ⊕ ℤ/2ℤ`
* `H₂(Klein; ℤ) = 0`

Isolated in its own file (as with `RP2Cert`) so that iterating on bridge-level
theorems does not retrigger the slow Sage SNF call.
-/

/-- Build the H₁ certificate via the `homology` tactic (term-mode), avoiding
`homology_cert`'s slow per-field `addAbbrevDecl`. -/
noncomputable def kleinBottleH1Cert : CertificateHomology (R := ℤ) kleinBottleFFC 1 := by
  homology kleinBottleFFC, 1

/-- The certified `H₁` of the Klein bottle is the group read from the
certificate. -/
theorem kleinBottleH1_correct :
    Nonempty (kleinBottleH1Cert.homologyModule ≃ₗ[ℤ]
      kleinBottleH1Cert.certifiedHomologyGroup) :=
  kleinBottleH1Cert.homology_is_certified_group
