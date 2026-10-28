module
public import Linear.NativeFiniteGradedSourceAmbientOrderedCech
public import Linear.NativeProjectiveTwistRegrading
public import Linear.OrderedFormalCechFunctoriality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ c : R,c ∈ A n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite R M] [Module.Finite S M]
variable {ι : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
open CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
/-- An actual isomorphism of the SAME abelian-sheaf coefficients induces an
isomorphism of their ORIGINAL ordered Cech complexes,including all signs. -/
def orderedTopAbelianCechCoefficientIso {X : Scheme.{u}} {κ : Type u} [LinearOrder κ]
    (U : κ → X.Opens) {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ≅ G) :
    orderedTopAbelianCechComplex X U F ≅ orderedTopAbelianCechComplex X U G :=
  orderedFormalCechComplexIso U
    ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).mapIso
      ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso e))
/-- EVERY integer twist of the SAME original finite graded module has the
actual source/ambient ordered Cech comparison.The regrading and its actual
sheaf isomorphism are constructed,not supplied as a certificate. -/
def nativeFiniteGradedSourceAmbientOrderedTwistCechIso
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenS : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤) (k : ℤ) :
    orderedTopAbelianCechComplex (Proj A) (fun i => Proj.basicOpen A (a i))
      ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR k)) ≅
      orderedTopAbelianCechComplex (Proj B) (fun i => Proj.basicOpen B (algebraMap R S (a i)))
        ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS k)) := by
  let Dk := integerGradingShift D k
  let hRk := integerGradingShift_smul_homogeneous A D hR k
  let hSk := integerGradingShift_smul_homogeneous B D hS k
  letI : DirectSum.Decomposition Dk := integerGradingShiftDecomposition D k
  let e := nativeFiniteGradedSourceAmbientOrderedCechIso A B Dk hRk hSk a ha hgenR hgenS
  let eA := orderedTopAbelianCechCoefficientIso (fun i => Proj.basicOpen A (a i))
    ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso (nativeProjectiveTwistRegradingIso A D hR k))
  let eB := orderedTopAbelianCechCoefficientIso (fun i => Proj.basicOpen B (algebraMap R S (a i)))
    ((schemeModuleToActualAbelianSheaf (Proj B)).mapIso (nativeProjectiveTwistRegradingIso B D hS k))
  exact eA.symm ≪≫ e ≪≫ eB
end LinearStudy
