module
public import Linear.NativeGeneralSourceAmbientCechProductFamilyCoefficient
public import Linear.NativeGeneralSourceAmbientOrderedCech
public import Linear.OrderedCrossSpaceProductChartCoefficient
public import Linear.NativeGeneralSourceAmbientCechObjects
public import Linear.ConcreteAdditiveEquivNaturality
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
set_option diagnostics true
set_option diagnostics.threshold 100
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M N : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module K N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hRD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hSD : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hRE : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (hSE : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
variable [DirectSum.Decomposition D] [DirectSum.Decomposition E]
variable [IsScalarTower K R M] [IsScalarTower K S M]
variable [IsScalarTower K R N] [IsScalarTower K S N]
variable [IsDomain R] [IsDomain S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [Module.Finite R M] [Module.Finite S M] [Module.Finite R N] [Module.Finite S N]
variable {ι κ : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
attribute [local irreducible] orderedFormalCechComplex FormalCoproduct.evalOp
attribute [local irreducible] nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
  schemeModuleToActualAbelianSheaf nativeIndependentSourceAmbientCechProductFamily_general
  nativeIndependentSourceAmbientCechProductIso_general
attribute [local irreducible] orderedCrossSpaceAbelianCechComplexIso
  orderedCrossSpaceAbelianCechComplexIso_of_productCharts
  abelianOpenSectionComparisonIso
/-- Original product-chart coefficient-square constructor with the source face condition proved. -/
def nativeIndependentSourceAmbientOrderedCechCoefficientBuilder_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) :=
  let FA := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hRD 0)).obj
  let FA' := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A E hRE 0)).obj
  let FB := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hSD 0)).obj
  let FB' := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B E hSE 0)).obj
  orderedCrossSpaceAbelianCechComplexIso_of_productCharts_coefficient
    (X:=Proj A) (Y:=Proj B) (ι:=ι) FA FA' FB FB'
    (fun i => Proj.basicOpen A (a i)) (fun i => Proj.basicOpen B (algebraMap R S (a i)))
    (nativeCechProductOpen A a) (nativeBaseSourceCechProductOpen B a)
    (fun p t => nativeProjective_cechIntersection_eq_basicOpen A a p t.1)
    (fun p t => nativeSourceCoordinateCechIntersection_eq_basicOpen B a p t.1)
    (nativeCechProductFace A a) (nativeBaseSourceCechProductFace B a)
    (nativeIndependentSourceAmbientCechProductFamily_general A B D hRD hSD a ha c hc hgenR hgenC)
    (nativeIndependentSourceAmbientCechProductFamily_face_general A B D hRD hSD a ha c hc hgenR hgenC)
end LinearStudy
