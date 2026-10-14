module
public import Linear.ProjectiveGradedDualCoefficientMatrix
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
variable {R S : Type} [CommRing R] [CommRing S] {σ : Type}
variable {I J : Type} [Finite I] [Finite J]

/-- The ACTUAL cokernels of ORIGINAL graded dual matrices agree under
the constructed original coefficient comparison. Reuses actual cokernel
mapIso and preservation by scalar restriction along the original ring
EQUIVALENCE;no cokernel comparison is an input. -/
def projectiveGradedDualCoefficientCokernelIso (e : R ≃+* S)
    (a : I → ℕ) (b : J → ℕ) (p : ∀ i j, homogeneousSubmodule σ R (a i-b j)) :
    cokernel (projectiveHomogeneousGradedPolynomialDualMatrix a b p) ≅
      (ModuleCat.restrictScalars e.toRingHom).obj
        (cokernel (projectiveHomogeneousGradedPolynomialDualMatrix a b
          (fun i j => projectiveHomogeneousCoefficientEquiv e (a i-b j) (p i j)))) :=
  (cokernel.mapIso _ _ (projectiveFiniteHomogeneousDualCoefficientIso e a)
    (projectiveFiniteHomogeneousDualCoefficientIso e b)
    (projectiveFiniteHomogeneousDualCoefficientIso_matrix e a b p)).trans
      (PreservesCokernel.iso (ModuleCat.restrictScalars e.toRingHom)
        (projectiveHomogeneousGradedPolynomialDualMatrix a b
          (fun i j => projectiveHomogeneousCoefficientEquiv e (a i-b j) (p i j)))).symm

/-- The proved cokernel comparison preserves the ORIGINAL quotient
map,not only the isomorphism class of its source and target. -/
theorem projectiveGradedDualCoefficientCokernelIso_quotient (e : R ≃+* S)
    (a : I → ℕ) (b : J → ℕ) (p : ∀ i j, homogeneousSubmodule σ R (a i-b j)) :
    cokernel.π (projectiveHomogeneousGradedPolynomialDualMatrix a b p) ≫
        (projectiveGradedDualCoefficientCokernelIso e a b p).hom =
      (projectiveFiniteHomogeneousDualCoefficientIso e b).hom ≫
        (ModuleCat.restrictScalars e.toRingHom).map
          (cokernel.π (projectiveHomogeneousGradedPolynomialDualMatrix a b
            (fun i j => projectiveHomogeneousCoefficientEquiv e (a i-b j) (p i j)))) := by
  unfold projectiveGradedDualCoefficientCokernelIso
  simp only [Iso.trans_hom,Iso.symm_hom]
  erw [cokernel.mapIso_hom]
  simp [cokernel.map,PreservesCokernel.iso_inv,π_comp_cokernelComparison]

/-- Canonical original K/Gamma cokernel comparison for the exact matrix
already appearing in the ACTUAL native top-Cech theorem. GammaSpecIso is
used internally;no ring equivalence or comparison square is an input. -/
def coordinateCanonicalGradedDualCoefficientCokernelIso
    (K : Type) [Field K] [Fintype σ] [LinearOrder σ]
    (a : I → ℕ) (b : J → ℕ) (p : ∀ i j, homogeneousSubmodule σ K (a i-b j)) :
    cokernel (projectiveHomogeneousGradedPolynomialDualMatrix a b p) ≅
      (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
        (cokernel (coordinateCanonicalGradedPolynomialDualMatrix a b p)) :=
  projectiveGradedDualCoefficientCokernelIso (coordinateCanonicalCoefficientRingEquiv K) a b p

/-- The actual canonical matrix cokernel alignment respects its original
quotient map,including every negative-degree zero entry. -/
theorem coordinateCanonicalGradedDualCoefficientCokernelIso_quotient
    (K : Type) [Field K] [Fintype σ] [LinearOrder σ]
    (a : I → ℕ) (b : J → ℕ) (p : ∀ i j, homogeneousSubmodule σ K (a i-b j)) :
    cokernel.π (projectiveHomogeneousGradedPolynomialDualMatrix a b p) ≫
        (coordinateCanonicalGradedDualCoefficientCokernelIso K a b p).hom =
      (coordinateCanonicalFiniteHomogeneousDualCoefficientIso K b).hom ≫
        (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
          (cokernel.π (coordinateCanonicalGradedPolynomialDualMatrix a b p)) :=
  projectiveGradedDualCoefficientCokernelIso_quotient
    (coordinateCanonicalCoefficientRingEquiv K) a b p

end MvPolynomial
