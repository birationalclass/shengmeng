module
public import Linear.IntegerFinitePresentationCoordinateNaturality
public import Linear.OrderedModuleCechActualCoefficientMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
/-- Forgetting the ORIGINAL canonical base-scalar restriction of the
ORIGINAL coordinate Cech homology map gives EXACTLY the old original
module-valued Cech coefficient homology map after its original forgetting.
This is an identity of maps;no naturality square is an input. -/
theorem coordinateNativeCechHomologyFunctor_map_forget
    {M N : (Proj (homogeneousSubmodule σ K)).Modules} (f : M ⟶ N) (q : ℕ) :
    (forget₂ (ModuleCat K) AddCommGrpCat).map
      ((ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
        ((coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) q).map f)) =
    (forget₂ (ModuleCat (coordinateCanonicalBaseRing K)) AddCommGrpCat).map
      (HomologicalComplex.homologyMap
        (LinearStudy.orderedBaseCechActualCoefficientMap (homogeneousProjπ (R:=K) (σ:=σ))
          f (coordinateOpenCover (R:=K) (σ:=σ))) (q+1)) := by
  rfl
end MvPolynomial
