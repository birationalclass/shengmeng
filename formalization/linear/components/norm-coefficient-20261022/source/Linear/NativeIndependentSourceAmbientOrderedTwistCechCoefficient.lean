module
public import Linear.NativeIndependentSourceAmbientOrderedCechCoefficient
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
/-- EVERY integer twist of the SAME source/ambient ordered Cech comparison
is natural for the ORIGINAL degree-zero S-linear map between TWO finite
graded modules. The TWO O-linear regrading squares are proved on actual
localized values;all product/intersection/face/sign comparisons are original. -/
theorem nativeIndependentSourceAmbientOrderedTwistCechIso_coefficient
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) :
    let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map
      (nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf k)
    let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
      (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf k)
    (nativeIndependentSourceAmbientOrderedTwistCechIso A B D hRD hSD a ha c hc hgenR hgenC k).hom ≫
      orderedTopAbelianCechCoefficientMap (Proj B) (fun i => Proj.basicOpen B (algebraMap R S (a i))) fB =
    orderedTopAbelianCechCoefficientMap (Proj A) (fun i => Proj.basicOpen A (a i)) fA ≫
      (nativeIndependentSourceAmbientOrderedTwistCechIso A B E hRE hSE a ha c hc hgenR hgenC k).hom := by
  let Dk := integerGradingShift D k
  let Ek := integerGradingShift E k
  let hRDk := integerGradingShift_smul_homogeneous A D hRD k
  let hSDk := integerGradingShift_smul_homogeneous B D hSD k
  let hREk := integerGradingShift_smul_homogeneous A E hRE k
  let hSEk := integerGradingShift_smul_homogeneous B E hSE k
  let hfk := fun j x hx => hf (j+k) x hx
  letI : DirectSum.Decomposition Dk := integerGradingShiftDecomposition D k
  letI : DirectSum.Decomposition Ek := integerGradingShiftDecomposition E k
  let U := fun i => Proj.basicOpen A (a i)
  let V := fun i => Proj.basicOpen B (algebraMap R S (a i))
  let eAD := orderedTopAbelianCechCoefficientIso U
    ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso (nativeProjectiveTwistRegradingIso A D hRD k))
  let eAE := orderedTopAbelianCechCoefficientIso U
    ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso (nativeProjectiveTwistRegradingIso A E hRE k))
  let eBD := orderedTopAbelianCechCoefficientIso V
    ((schemeModuleToActualAbelianSheaf (Proj B)).mapIso (nativeProjectiveTwistRegradingIso B D hSD k))
  let eBE := orderedTopAbelianCechCoefficientIso V
    ((schemeModuleToActualAbelianSheaf (Proj B)).mapIso (nativeProjectiveTwistRegradingIso B E hSE k))
  let eD := nativeIndependentSourceAmbientOrderedCechIso A B Dk hRDk hSDk a ha c hc hgenR hgenC
  let eE := nativeIndependentSourceAmbientOrderedCechIso A B Ek hREk hSEk a ha c hc hgenR hgenC
  let muAk := orderedTopAbelianCechCoefficientMap (Proj A) U ((schemeModuleToActualAbelianSheaf (Proj A)).map
    (nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf k))
  let muA0 := orderedTopAbelianCechCoefficientMap (Proj A) U ((schemeModuleToActualAbelianSheaf (Proj A)).map
    (nativeProjectiveDegreeZeroSheafMap A Dk Ek hRDk hREk (f.restrictScalars R) hfk 0))
  let muBk := orderedTopAbelianCechCoefficientMap (Proj B) V ((schemeModuleToActualAbelianSheaf (Proj B)).map
    (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf k))
  let muB0 := orderedTopAbelianCechCoefficientMap (Proj B) V ((schemeModuleToActualAbelianSheaf (Proj B)).map
    (nativeProjectiveDegreeZeroSheafMap B Dk Ek hSDk hSEk f hfk 0))
  have hA : CommSq muAk eAD.inv eAE.inv muA0 :=
    ⟨nativeOrderedCechRegradingIso_coefficient_inv A D E hRD hRE (f.restrictScalars R) hf U k⟩
  have hB : CommSq muB0 eBD.hom eBE.hom muBk :=
    ⟨nativeOrderedCechRegradingIso_coefficient_hom B D E hSD hSE f hf V k⟩
  have h0 : CommSq muA0 eD.hom eE.hom muB0 :=
    ⟨(nativeIndependentSourceAmbientOrderedCechIso_coefficient A B Dk Ek hRDk hSDk hREk hSEk f hfk
      a ha c hc hgenR hgenC).symm⟩
  change (eAD.inv ≫ eD.hom ≫ eBD.hom) ≫ muBk = muAk ≫ (eAE.inv ≫ eE.hom ≫ eBE.hom)
  exact (hA.vert_comp (h0.vert_comp hB)).w.symm
end LinearStudy
