import ChainCert.Homology.Tactic
import ChainCert.Homology.Bridge
import ChainCert.Examples.Complexes

/-!
# Homology tactic examples

This file shows the basic user-facing modes of the `homology` tactic.
-/

/-- `homology X, k` can add a named certificate to the local context. -/
example : True := by
  homology triangleFFC, 1
  trivial

/-- `homology X, k as h` chooses the local certificate name. -/
example : True := by
  homology triangleFFC, 1 as hTri
  have _ :
      CertificateHomology (R := ℤ) triangleFFC 1 := hTri
  have _ :
      hTri.homologyModule ≃ₗ[ℤ] hTri.certifiedHomologyGroup := hTri.correct
  have _ :
      Nonempty (hTri.homologyModule ≃ₗ[ℤ] hTri.certifiedHomologyGroup) :=
    hTri.homology_is_certified_group
  trivial

/-- `homology X, k` closes a matching `CertificateHomology` goal. -/
example : CertificateHomology (R := ℤ) triangleFFC 1 := by
  homology triangleFFC, 1
