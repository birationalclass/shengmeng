module
public import Linear.NativeIndependentNormalizationActualHCoefficient
public import Linear.NativeIndependentNormalizationHFactorization
public import Linear.OrderedModuleCechActualAbelianHomology
public import Linear.NativeIndependentNormalizationActualHFactorization
public import Linear.NativeProjActualHCoefficientNaturality
public import Linear.NativeProjectiveTwistQuasicoherent
public import Linear.FiniteNormalizationCoordinateCover
public import Linear.NativeProjActualHComparison
public import Linear.NativeProjectiveTwistFinitePresentation
public import Linear.NativeIndependentSourceAmbientOrderedTwistCech
public import Linear.NativeOrderedCechRegradingCoefficient
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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option diagnostics true
set_option diagnostics.threshold 1000
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
variable [Finite ι] [Algebra.FiniteType K S] [Module.Finite R S]
attribute [local irreducible] finiteTypeNativeProj_orderedActualHigherHIso
  noetherianFiniteOrderedAffineCover_actualHigherHIso topFiniteOrderedCech_actualHigherHIso_of_localAcyclic
  nativeIndependentSourceAmbientOrderedTwistCechIso orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso
/-- The SAME original module-valued ambient-Cech/source-H comparison is
natural for the ORIGINAL degree-zero map,EVERY integer twist and positive
degree. Original module-homology forgetting and actual coefficient maps
are retained;no comparison square is supplied as a hypothesis. -/
theorem nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_coefficient
    {Y : Scheme.{u}} (pi : Proj A ⟶ Y)
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    let phiA := orderedBaseCechActualCoefficientMap pi
      (nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf k)
      (fun i => Proj.basicOpen A (a i))
    let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
      (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf k)
    (forget₂ (ModuleCat.{u} Γ(Y,⊤)) AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap phiA (q+1)) ≫
      (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B E hRE hSE a ha c hc pi hgenR hgenC k q).hom =
    (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hRD hSD a ha c hc pi hgenR hgenC k q).hom ≫
      (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map fB := by
  let MA := nativeProjectiveModuleSheaf A D hRD k
  let NA := nativeProjectiveModuleSheaf A E hRE k
  let U := fun i => Proj.basicOpen A (a i)
  let fA0 := nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf k
  let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map fA0
  let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
    (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf k)
  let phiA := orderedBaseCechActualCoefficientMap pi fA0 U
  let mA := orderedTopAbelianCechCoefficientMap (Proj A) U fA
  let H := forget₂ (ModuleCat.{u} Γ(Y,⊤)) AddCommGrpCat.{u}
  let eM := orderedModuleCechActualAbelianHomologyIso pi MA U (q+1)
  let eN := orderedModuleCechActualAbelianHomologyIso pi NA U (q+1)
  let jM := nativeIndependentFiniteNormalization_actualHigherHIso A B D hRD hSD a ha c hc hgenR hgenC k q
  let jN := nativeIndependentFiniteNormalization_actualHigherHIso A B E hRE hSE a ha c hc hgenR hgenC k q
  have h1 : CommSq (H.map (HomologicalComplex.homologyMap phiA (q+1))) eM.hom eN.hom
      (HomologicalComplex.homologyMap mA (q+1)) :=
    ⟨orderedModuleCechActualAbelianHomologyIso_coefficient_naturality pi fA0 U (q+1)⟩
  have h2 : CommSq (HomologicalComplex.homologyMap mA (q+1)) jM.hom jN.hom
      ((CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map fB) :=
    ⟨nativeIndependentFiniteNormalization_actualHigherHIso_coefficient A B D E hRD hSD hRE hSE f hf
      a ha c hc hgenR hgenC k q⟩
  simp only [nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_factorization,Iso.trans_hom]
  exact (h1.vert_comp h2).w
end LinearStudy
