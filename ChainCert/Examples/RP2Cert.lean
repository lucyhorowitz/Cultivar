import ChainCert.Examples.Complexes
import ChainCert.Boundary.Verify
import ChainCert.SNF.Tactic
import ChainCert.Homology.Tactic
import ChainCert.Homology.Command
import ChainCert.Homology.Bridge

/-!
# `H₁(ℝP²)` certificate

Sage-checked `CertificateHomology` for the real projective plane. Isolated
in its own file so that iterating on bridge-level theorems does not retrigger
the (slow) Sage SNF call.
-/

/-- The `H₁` certificate for the real projective plane, produced by the
`homology` pipeline from a Sage-checked SNF. -/
noncomputable def rp2H1Cert : CertificateHomology (R := ℤ) rp2FFC 1 := by
  homology rp2FFC, 1
