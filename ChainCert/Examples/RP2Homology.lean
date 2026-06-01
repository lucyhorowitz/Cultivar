import ChainCert.Examples.RP2Cert
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# Worked example: `H₁(ℝP²; ℤ)` has order-2 torsion

The real projective plane is the smallest closed surface whose integral
homology has torsion. Its minimal triangulation `rp2FFC` has 6 vertices,
15 edges, and 10 triangles. The `H₁` certificate is built in
`ChainCert.Examples.RP2Cert`; here we read off the torsion factor from the
diagonal Smith form via `CertificateHomology.correct`.
-/

/-- The certified `H₁` of `ℝP²` is the group read from the certificate. -/
theorem rp2H1_correct :
    Nonempty (rp2H1Cert.homologyModule ≃ₗ[ℤ]
      rp2H1Cert.certifiedHomologyGroup) :=
  rp2H1Cert.homology_is_certified_group

/-! ### Torsion structure of `H₁(ℝP²)`

We probe the Sage-certified diagonal: it has 10 entries, exactly one of which
is non-unit, and that entry is `±2`. So among the ten factors of
`certifiedHomologyGroup`, nine are trivial and one is `ℤ/2ℤ`. -/

/-- The diagonal index set has 10 elements. -/
theorem rp2_presentation_size :
    Fintype.card rp2H1Cert.certifiedHomologyIndex = 10 := by
  unfold rp2H1Cert
  native_decide

/-- Exactly one diagonal entry of the certified Smith form is non-unit. -/
theorem rp2_unique_non_unit_diagonal :
    (Finset.univ.filter (fun i : rp2H1Cert.certifiedHomologyIndex =>
      ¬ IsUnit (rp2H1Cert.certifiedHomologyDiagonal i))).card = 1 := by
  unfold rp2H1Cert
  native_decide

/-- The unique non-unit diagonal entry has absolute value `2`. -/
theorem rp2_torsion_diagonal_is_two
    (i : rp2H1Cert.certifiedHomologyIndex)
    (hi : ¬ IsUnit (rp2H1Cert.certifiedHomologyDiagonal i)) :
    (rp2H1Cert.certifiedHomologyDiagonal i).natAbs = 2 := by
  revert i hi
  unfold rp2H1Cert
  native_decide
