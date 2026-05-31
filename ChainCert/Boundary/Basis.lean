import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import ChainCert.SimplicialComplex
import Init.Data.List.Sort.Basic
import ChainCert.Boundary.Spec

variable {ι : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι]

/- Basis layer notes:

This module should define canonical `k`-simplex basis enumeration used by the
boundary verifier (spec side), while keeping Sage transport concerns separate.

- Spec side: basis elements are oriented simplices in vertex type `ι`.
- Interop side: `FiniteFacetComplex.toRawFacets` encodes facets as `Nat` lists
  for JSON exchange with Sage. -/

def isFaceOf (F : FiniteFacetComplex ι) (s : Finset ι) : Prop :=
  s.Nonempty ∧ ∃ f ∈ F.facets, s ⊆ f

def isKFaceOf (F : FiniteFacetComplex ι) (k : ℕ) (s : Finset ι) : Prop :=
  s.card = k + 1 ∧ ∃ f ∈ F.facets, s ⊆ f

instance (F : FiniteFacetComplex ι) (k : Nat) : DecidablePred (fun s : Finset ι => isKFaceOf F k s) := by
  intro s
  unfold isKFaceOf
  infer_instance

def kFaces (F : FiniteFacetComplex ι) (k : Nat) : Finset (Finset ι) :=
  ((Finset.univ : Finset ι).powerset).filter (fun s => isKFaceOf F k s)

def encodeVertexOrder : List ι :=
  (Finset.univ : Finset ι).sort (· ≤ ·)

def encodeSimplex (σ : List ι) : List Nat :=
  σ.map (encodeVertexOrder.idxOf ·)

@[reducible]
def canonicalBasisRaw (F : FiniteFacetComplex ι) (k : Nat) : List (List Nat) :=
  let verts := encodeVertexOrder (ι := ι)
  let candidates := verts.sublistsLen (k + 1)
  let faces := candidates.filter (fun σ => decide (isKFaceOf F k σ.toFinset))
  (faces.map encodeSimplex).mergeSort (· ≤ ·)

def validDomainBasis (F : FiniteFacetComplex ι) (k : Nat) (dom : List (List Nat)) : Prop :=
  dom = canonicalBasisRaw F k

def validCodomainBasis (F : FiniteFacetComplex ι) (k : Nat) (cod : List (List Nat)) : Prop :=
  cod = (if k = 0 then [] else canonicalBasisRaw F (k - 1))

instance (F : FiniteFacetComplex ι) (k : Nat) (dom : List (List Nat)) :
    Decidable (validDomainBasis F k dom) := by
  unfold validDomainBasis
  infer_instance

instance (F : FiniteFacetComplex ι) (k : Nat) (cod : List (List Nat)) :
    Decidable (validCodomainBasis F k cod) := by
  unfold validCodomainBasis
  infer_instance

@[reducible]
def cellCount (F : FiniteFacetComplex ι) (k : Nat) : Nat :=
  (canonicalBasisRaw F k).length

def boundaryMatrix (F : FiniteFacetComplex ι) (k : Nat) :
    Matrix (Fin (cellCount F k)) (Fin (cellCount F (k+1))) ℤ :=
  Matrix.of fun (i : Fin (cellCount F k)) (j : Fin
  (cellCount F (k+1))) =>
      boundaryCoeff
        ((canonicalBasisRaw F (k+1))[j.val]'j.isLt)
        ((canonicalBasisRaw F k)[i.val]'i.isLt)
