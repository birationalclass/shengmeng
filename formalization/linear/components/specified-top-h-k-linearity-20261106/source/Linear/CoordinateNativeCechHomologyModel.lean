module
public import Linear.NativeProjectiveMatrixHomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Explicit identity bridge from the ORIGINAL composed homology functor
object to its SAME ordered-Cech homology object. Keep geometric coefficients abstract. -/
def coordinateNativeCechHomologyFunctorModelIso (q : ℕ)
    (M : (Proj (homogeneousSubmodule σ K)).Modules) :
    (coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) q).obj M ≅
      (Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R:=K) (σ:=σ)) M
        (coordinateOpenCover (R:=K) (σ:=σ))).homology (q+1) := Iso.refl _
/-- This bridge changes no element. -/
theorem coordinateNativeCechHomologyFunctorModelIso_apply (q : ℕ)
    (M : (Proj (homogeneousSubmodule σ K)).Modules)
    (x : (coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) q).obj M) :
    (coordinateNativeCechHomologyFunctorModelIso q M).hom x = x := rfl
end MvPolynomial
