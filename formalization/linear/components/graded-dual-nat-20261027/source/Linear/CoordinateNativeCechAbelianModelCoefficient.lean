module
public import Linear.CoordinateNativeCechAbelianModel
public import Linear.CoordinateCechCoefficientForgettingIdentity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The identity bridge is natural for the ORIGINAL module-Cech coefficient map.
Both geometric modules and their original map are arbitrary. -/
theorem coordinateNativeCechAbelianModelIso_coefficient
    {M N : (Proj (homogeneousSubmodule σ K)).Modules} (f : M ⟶ N) (q : ℕ) :
    CommSq
      ((forget₂ (ModuleCat (coordinateCanonicalBaseRing K)) AddCommGrpCat).map
        (HomologicalComplex.homologyMap
          (LinearStudy.orderedBaseCechActualCoefficientMap (homogeneousProjπ (R:=K) (σ:=σ))
            f (coordinateOpenCover (R:=K) (σ:=σ))) (q+1)))
      (coordinateNativeCechAbelianModelIso q M).inv
      (coordinateNativeCechAbelianModelIso q N).inv
      ((forget₂ (ModuleCat K) AddCommGrpCat).map
        ((ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
          ((coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) q).map f))) := by
  constructor
  rfl
end MvPolynomial
