module
public import Linear.NativeIndependentSourceAmbientCechIntersectionCoefficient
public import Linear.NativeIndependentSourceAmbientOrderedCech
public import Linear.OrderedFreeSheafHomCoefficientNaturality
public import Linear.OrderedCrossSpaceCechCoefficientNaturality
public import Linear.NativeIndependentSourceAmbientCechObjects
public import Linear.ConcreteAdditiveEquivNaturality
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
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
variable [IsDomain S] [Module.IsTorsionFree S M] [Module.IsTorsionFree S N]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [Module.Finite R M] [Module.Finite S M] [Module.Finite R N] [Module.Finite S N]
variable {ι κ : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
/-- The SAME existing source/ambient ordered Cech comparisons are natural
for the ORIGINAL degree-zero map between TWO finite graded modules. All
intersection squares are derived;original faces,signs and maps are retained. -/
theorem nativeIndependentSourceAmbientOrderedCechIso_coefficient
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) :
    let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map
      (nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf 0)
    let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
      (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf 0)
    (nativeIndependentSourceAmbientOrderedCechIso A B D hRD hSD a ha c hc hgenR hgenC).hom ≫
      orderedTopAbelianCechCoefficientMap (Proj B) (fun i => Proj.basicOpen B (algebraMap R S (a i))) fB =
    orderedTopAbelianCechCoefficientMap (Proj A) (fun i => Proj.basicOpen A (a i)) fA ≫
      (nativeIndependentSourceAmbientOrderedCechIso A B E hRE hSE a ha c hc hgenR hgenC).hom := by
  let FA := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hRD 0)).obj
  let FA' := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A E hRE 0)).obj
  let FB := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hSD 0)).obj
  let FB' := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B E hSE 0)).obj
  let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map
    (nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf 0)
  let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
    (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf 0)
  exact orderedCrossSpaceAbelianCechComplexIso_coefficient FA FA' FB FB'
    (fun i => Proj.basicOpen A (a i)) (fun i => Proj.basicOpen B (algebraMap R S (a i)))
    (fun p t => nativeIndependentSourceAmbientCechIntersectionIso A B D hRD hSD a ha c hc hgenR hgenC p t.1)
    (fun p k t => nativeIndependentSourceAmbientCechIntersectionIso_face A B D hRD hSD a ha c hc hgenR hgenC p k t)
    (fun p t => nativeIndependentSourceAmbientCechIntersectionIso A B E hRE hSE a ha c hc hgenR hgenC p t.1)
    (fun p k t => nativeIndependentSourceAmbientCechIntersectionIso_face A B E hRE hSE a ha c hc hgenR hgenC p k t)
    fA.hom fB.hom
    (fun p t => nativeIndependentSourceAmbientCechIntersectionIso_coefficient A B D E hRD hSD hRE hSE f hf
      a ha c hc hgenR hgenC p t.1)
end LinearStudy
