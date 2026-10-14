module
public import Linear.ProjectiveDualCoefficientRestriction
public import Linear.NativePolynomialMatrixTopDuality
public import Linear.BiproductMatrixNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
variable {R S : Type} [CommRing R] [CommRing S] {σ : Type}
variable {I J : Type} [Finite I] [Finite J]

/-- The ORIGINAL homogeneous graded dual-entry matrix over its ORIGINAL
coefficient ring. Every negative multiplying degree has a zero entry. -/
def projectiveHomogeneousGradedPolynomialDualMatrix
    (a : I → ℕ) (b : J → ℕ) (p : ∀ i j, homogeneousSubmodule σ R (a i-b j)) :
    (⨁ fun i => ModuleCat.of R (Module.Dual R (homogeneousSubmodule σ R (a i)))) ⟶
      (⨁ fun j => ModuleCat.of R (Module.Dual R (homogeneousSubmodule σ R (b j)))) :=
  biproduct.matrix (fun i j => projectiveHomogeneousGradedPolynomialDualEntry
    (a i) (b j) (p i j))

/-- Assemble the already constructed ORIGINAL dual coefficient maps,
using original finite biproduct preservation under mathlib scalar restriction. -/
def projectiveFiniteHomogeneousDualCoefficientIso (e : R ≃+* S) (a : I → ℕ) :
    (⨁ fun i => ModuleCat.of R (Module.Dual R (homogeneousSubmodule σ R (a i)))) ≅
      (ModuleCat.restrictScalars e.toRingHom).obj
        (⨁ fun i => ModuleCat.of S (Module.Dual S (homogeneousSubmodule σ S (a i)))) :=
  (biproduct.mapIso (fun i => projectiveHomogeneousDualCoefficientIso (σ := σ) e (a i))).trans
    ((ModuleCat.restrictScalars e.toRingHom).mapBiproduct
      (fun i => ModuleCat.of S (Module.Dual S (homogeneousSubmodule σ S (a i))))).symm

/-- The WHOLE ORIGINAL graded dual matrix commutes with the constructed
coefficient comparison and original scalar restriction. The entry square
is proved,including negative zeros and genuine degree equality transports. -/
theorem projectiveFiniteHomogeneousDualCoefficientIso_matrix (e : R ≃+* S)
    (a : I → ℕ) (b : J → ℕ) (p : ∀ i j, homogeneousSubmodule σ R (a i-b j)) :
    projectiveHomogeneousGradedPolynomialDualMatrix a b p ≫
        (projectiveFiniteHomogeneousDualCoefficientIso e b).hom =
      (projectiveFiniteHomogeneousDualCoefficientIso e a).hom ≫
        (ModuleCat.restrictScalars e.toRingHom).map
          (projectiveHomogeneousGradedPolynomialDualMatrix a b
            (fun i j => projectiveHomogeneousCoefficientEquiv e (a i-b j) (p i j))) := by
  let F := ModuleCat.restrictScalars e.toRingHom
  let u := fun i j => projectiveHomogeneousGradedPolynomialDualEntry (a i) (b j) (p i j)
  let v := fun i j => projectiveHomogeneousGradedPolynomialDualEntry (a i) (b j)
    (projectiveHomogeneousCoefficientEquiv e (a i-b j) (p i j))
  have he := LinearStudy.biproductMatrixComponentNaturality u
    (fun i j => F.map (v i j))
    (fun i => (projectiveHomogeneousDualCoefficientIso e (a i)).hom)
    (fun j => (projectiveHomogeneousDualCoefficientIso e (b j)).hom)
    (fun i j => projectiveHomogeneousDualCoefficientIso_gradedEntry e (a i) (b j) (p i j))
  have hn := LinearStudy.additiveFunctorBiproductMatrixNaturality F v
  let ea := F.mapBiproduct
    (fun i => ModuleCat.of S (Module.Dual S (homogeneousSubmodule σ S (a i))))
  let eb := F.mapBiproduct
    (fun j => ModuleCat.of S (Module.Dual S (homogeneousSubmodule σ S (b j))))
  have ht : biproduct.matrix (fun i j => F.map (v i j)) ≫ eb.inv =
      ea.inv ≫ F.map (biproduct.matrix v) := by
    calc
      _ = ea.inv ≫ (ea.hom ≫ biproduct.matrix (fun i j => F.map (v i j))) ≫ eb.inv := by simp
      _ = ea.inv ≫ (F.map (biproduct.matrix v) ≫ eb.hom) ≫ eb.inv := by rw [← hn]
      _ = _ := by simp
  simp only [projectiveFiniteHomogeneousDualCoefficientIso,Iso.trans_hom,
    Iso.symm_hom,biproduct.mapIso_hom]
  change biproduct.matrix u ≫ biproduct.map (fun j => (projectiveHomogeneousDualCoefficientIso e (b j)).hom) ≫ eb.inv =
    (biproduct.map (fun i => (projectiveHomogeneousDualCoefficientIso e (a i)).hom) ≫ ea.inv) ≫ F.map (biproduct.matrix v)
  rw [← Category.assoc,he]
  simp only [Category.assoc]
  rw [ht]

/-- The ACTUAL canonical scalar comparison on the entire ORIGINAL
finite graded dual family uses GammaSpecIso,no chosen ring comparison. -/
def coordinateCanonicalFiniteHomogeneousDualCoefficientIso (K : Type) [CommRing K]
    (a : I → ℕ) :
    (⨁ fun i => ModuleCat.of K (Module.Dual K (homogeneousSubmodule σ K (a i)))) ≅
      (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
        (⨁ fun i => ModuleCat.of (coordinateCanonicalBaseRing K)
          (Module.Dual (coordinateCanonicalBaseRing K)
            (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) (a i)))) :=
  projectiveFiniteHomogeneousDualCoefficientIso (coordinateCanonicalCoefficientRingEquiv K) a

/-- The actual canonical matrix appearing in native top-Cech duality is
exactly the ORIGINAL K-coefficient matrix under the constructed canonical
scalar comparison. This proves the WHOLE matrix square. -/
theorem coordinateCanonicalFiniteHomogeneousDualCoefficientIso_matrix
    (K : Type) [Field K] [Fintype σ] [LinearOrder σ]
    (a : I → ℕ) (b : J → ℕ) (p : ∀ i j, homogeneousSubmodule σ K (a i-b j)) :
    projectiveHomogeneousGradedPolynomialDualMatrix a b p ≫
        (coordinateCanonicalFiniteHomogeneousDualCoefficientIso K b).hom =
      (coordinateCanonicalFiniteHomogeneousDualCoefficientIso K a).hom ≫
        (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
          (coordinateCanonicalGradedPolynomialDualMatrix a b p) :=
  projectiveFiniteHomogeneousDualCoefficientIso_matrix
    (coordinateCanonicalCoefficientRingEquiv K) a b p

end MvPolynomial
