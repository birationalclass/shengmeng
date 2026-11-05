module
public import Linear.ProjectiveHomogeneousDualCoefficientEquiv
public import Linear.ProjectiveCanonicalCoefficientEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace MvPolynomial
variable (K : Type) [CommRing K] {σ : Type}
attribute [local instance] coordinateCanonicalCoefficientInverseForward coordinateCanonicalCoefficientInverseBackward

/-- Change ORIGINAL homogeneous dual functionals using the ACTUAL
canonical affine coefficient comparison. Neither the ring comparison
nor the dual comparison is supplied as an input. -/
def coordinateCanonicalHomogeneousDualCoefficientEquiv (m : ℕ) :
    Module.Dual K (homogeneousSubmodule σ K m) ≃ₛₗ[(coordinateCanonicalCoefficientRingEquiv K).toRingHom]
      Module.Dual (coordinateCanonicalBaseRing K)
        (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) m) :=
  projectiveHomogeneousDualCoefficientEquiv (coordinateCanonicalCoefficientRingEquiv K) m

/-- The canonical dual uses the ORIGINAL inverse homogeneous coefficient
map and the ORIGINAL canonical scalar comparison. -/
theorem coordinateCanonicalHomogeneousDualCoefficientEquiv_apply (m : ℕ)
    (φ : Module.Dual K (homogeneousSubmodule σ K m))
    (q : homogeneousSubmodule σ (coordinateCanonicalBaseRing K) m) :
    coordinateCanonicalHomogeneousDualCoefficientEquiv K m φ q =
      coordinateCanonicalCoefficientRingEquiv K
        (φ ((coordinateCanonicalHomogeneousCoefficientEquiv K m).symm q)) := rfl

/-- The ACTUAL canonical dual coefficient map commutes with each
original homogeneous multiplication transpose. This is still a proved
entry square,not the whole original Cech/Hom cokernel comparison. -/
theorem coordinateCanonicalHomogeneousDualCoefficientEquiv_multiply (l m : ℕ)
    (p : homogeneousSubmodule σ K l)
    (φ : Module.Dual K (homogeneousSubmodule σ K (l+m))) :
    coordinateCanonicalHomogeneousDualCoefficientEquiv K m (projectiveHomogeneousMultiplyDual l m p φ) =
      projectiveHomogeneousMultiplyDual l m (coordinateCanonicalHomogeneousCoefficientEquiv K l p)
        (coordinateCanonicalHomogeneousDualCoefficientEquiv K (l+m) φ) :=
  projectiveHomogeneousDualCoefficientEquiv_multiply (coordinateCanonicalCoefficientRingEquiv K) l m p φ

end MvPolynomial
