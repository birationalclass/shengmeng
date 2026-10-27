module
public import Linear.CoordinateNativeCechHomologyModel
public import Linear.ProjectiveCanonicalCoefficientEquiv
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
/-- Identity on the SAME original Cech homology after its two exact scalar forgettings.
No coefficient,comparison or desired naturality square is an input. -/
def coordinateNativeCechAbelianModelIso (q : ℕ)
    (M : (Proj (homogeneousSubmodule σ K)).Modules) :
    (forget₂ (ModuleCat K) AddCommGrpCat).obj
      ((ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
        ((coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) q).obj M)) ≅
    (forget₂ (ModuleCat (coordinateCanonicalBaseRing K)) AddCommGrpCat).obj
      ((Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R:=K) (σ:=σ)) M
        (coordinateOpenCover (R:=K) (σ:=σ))).homology (q+1)) := Iso.refl _
end MvPolynomial
