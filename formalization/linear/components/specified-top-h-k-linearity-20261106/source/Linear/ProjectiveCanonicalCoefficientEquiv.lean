module
public import Linear.ProjectiveHomogeneousCoefficientEquiv
public import Linear.ProjectiveCanonicalResidue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry
variable (K : Type) [CommRing K] {σ : Type}

/-- The canonical ORIGINAL affine global-section coefficient comparison,
using mathlib Scheme.GammaSpecIso. No ring equivalence is an input. -/
abbrev coordinateCanonicalCoefficientRingEquiv : K ≃+* coordinateCanonicalBaseRing K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm

/-- Its forward inverse pair is derived from the canonical affine comparison. -/
local instance coordinateCanonicalCoefficientInverseForward :
    RingHomInvPair (coordinateCanonicalCoefficientRingEquiv K).toRingHom
      (coordinateCanonicalCoefficientRingEquiv K).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (coordinateCanonicalCoefficientRingEquiv K)

/-- Its reverse inverse pair is also derived,not assumed. -/
local instance coordinateCanonicalCoefficientInverseBackward :
    RingHomInvPair (coordinateCanonicalCoefficientRingEquiv K).symm.toRingHom
      (coordinateCanonicalCoefficientRingEquiv K).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (coordinateCanonicalCoefficientRingEquiv K)

/-- The ACTUAL canonical K-to-Gamma(Spec K,O) homogeneous coefficient map
is a semilinear equivalence,in every homogeneous degree. -/
def coordinateCanonicalHomogeneousCoefficientEquiv (m : ℕ) :
    homogeneousSubmodule σ K m ≃ₛₗ[(coordinateCanonicalCoefficientRingEquiv K).toRingHom]
      homogeneousSubmodule σ (coordinateCanonicalBaseRing K) m :=
  projectiveHomogeneousCoefficientEquiv (coordinateCanonicalCoefficientRingEquiv K) m

/-- Its original forward map is exactly the coefficient map already used
in the published native top-Cech polynomial matrix. -/
theorem coordinateCanonicalHomogeneousCoefficientEquiv_apply (m : ℕ)
    (p : homogeneousSubmodule σ K m) :
    coordinateCanonicalHomogeneousCoefficientEquiv K m p =
      projectiveHomogeneousCoefficientMap
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom m p := rfl

/-- The original inverse uses the actual inverse canonical affine coefficient map. -/
theorem coordinateCanonicalHomogeneousCoefficientEquiv_symm_apply (m : ℕ)
    (p : homogeneousSubmodule σ (coordinateCanonicalBaseRing K) m) :
    (coordinateCanonicalHomogeneousCoefficientEquiv K m).symm p =
      projectiveHomogeneousCoefficientMap
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toRingHom m p := rfl

/-- The ACTUAL canonical coefficient equivalence respects each original
homogeneous polynomial multiplication entry. -/
theorem coordinateCanonicalHomogeneousCoefficientEquiv_multiply (l m : ℕ)
    (p : homogeneousSubmodule σ K l) (q : homogeneousSubmodule σ K m) :
    coordinateCanonicalHomogeneousCoefficientEquiv K (l+m) (projectiveHomogeneousMultiply l m p q) =
      projectiveHomogeneousMultiply l m (coordinateCanonicalHomogeneousCoefficientEquiv K l p)
        (coordinateCanonicalHomogeneousCoefficientEquiv K m q) :=
  projectiveHomogeneousCoefficientEquiv_multiply (coordinateCanonicalCoefficientRingEquiv K) l m p q

end MvPolynomial
