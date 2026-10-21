module
public import Linear.NativeIndependentNormalizationModuleHPointwiseScalar
public import Linear.SchemeModuleActualHBaseScalars
public import Linear.OrderedModuleCechCoefficientScalar
public import Linear.NativeIndependentNormalizationActualHScalar
public import Linear.OrderedModuleCechActualAbelianHomology
public import Linear.FiniteNormalizationCoordinateCover
public import Linear.NativeProjActualHComparison
public import Linear.NativeProjectiveTwistFinitePresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite R S] [Module.Finite R M] [Module.Finite S M]
variable {ι κ : Type u} [LinearOrder ι] [Finite ι]
variable (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
attribute [local irreducible] nativeIndependentFiniteNormalization_moduleCechActualHigherHIso
  nativeIndependentFiniteNormalization_actualHigherHIso orderedModuleCechActualAbelianHomologyIso
  orderedModuleCechActualAbelianComplexIso orderedBaseCechActualCoefficientMap
/-- The SAME old finite-normalization module-Cech/actual-source-H map
is linear for the independently constructed ORIGINAL base action,in
EVERY integer twist and EVERY positive degree. -/
theorem nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_smul
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤))
    (x : (orderedBaseCechComplex (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))) (nativeProjectiveModuleSheaf A D hR k) (fun i => Proj.basicOpen A (a i))).homology (q+1)) :
    let piA := (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0))))
    let piB := (Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0))))
    letI := schemeModuleActualHBaseModule piB (nativeProjectiveModuleSheaf B D hS k) (q+1)
    (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hR hS a ha c hc piA hgenR hgenC k q).hom (r • x) =
      r • (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hR hS a ha c hc piA hgenR hgenC k q).hom x := by
  let piA := (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0))))
  let piB := (Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0))))
  let MA := nativeProjectiveModuleSheaf A D hR k
  let MB := nativeProjectiveModuleSheaf B D hS k
  let U := fun i => Proj.basicOpen A (a i)
  letI := schemeModuleActualHBaseModule piB MB (q+1)
  let C := orderedBaseCechComplex piA MA U
  let I := nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hR hS a ha c hc piA hgenR hgenC k q
  have h := nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_baseScalar_apply
    A B D hR hS a ha c hc hgenR hgenC k q r x
  have hs := orderedBaseCechActualCoefficientMap_originalScalar piA MA r U
  have hh := congrArg (fun g : C ⟶ C => HomologicalComplex.homologyMap g (q+1)) hs
  rw [actualHomologicalComplex_homologyMap_smul_id] at hh
  have hsx : HomologicalComplex.homologyMap
      (orderedBaseCechActualCoefficientMap piA (originalGlobalModuleScalar (piA.appTop r) MA) U)
      (q+1) x = r • x := ConcreteCategory.congr_hom hh x
  have targetScalar := schemeModuleActualHBaseModule_smul piB MB (q+1) r (I.hom x)
  exact ((congrArg (fun y => I.hom y) hsx).symm.trans h).trans targetScalar.symm
/-- Upgrade the SAME old additive comparison to a base-linear equivalence.
The actual H action was independently constructed from coefficient multiplication. -/
def nativeIndependentFiniteNormalization_moduleCechActualHigherHLinearEquiv
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    let piA := (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0))))
    let piB := (Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0))))
    letI := schemeModuleActualHBaseModule piB (nativeProjectiveModuleSheaf B D hS k) (q+1)
    (orderedBaseCechComplex piA (nativeProjectiveModuleSheaf A D hR k)
      (fun i => Proj.basicOpen A (a i))).homology (q+1) ≃ₗ[Γ(Spec (CommRingCat.of K),⊤)]
        schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1) := by
  let piA := (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0))))
  let piB := (Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0))))
  letI := schemeModuleActualHBaseModule piB (nativeProjectiveModuleSheaf B D hS k) (q+1)
  exact {
    (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hR hS a ha c hc piA hgenR hgenC k q).addCommGroupIsoToAddEquiv with
    map_smul' := fun r x => nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_smul
      A B D hR hS a ha c hc hgenR hgenC k q r x }
/-- Underlying function is EXACTLY the pre-existing original comparison. -/
theorem nativeIndependentFiniteNormalization_moduleCechActualHigherHLinearEquiv_apply
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ)
    (x : (orderedBaseCechComplex (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))) (nativeProjectiveModuleSheaf A D hR k) (fun i => Proj.basicOpen A (a i))).homology (q+1)) :
    nativeIndependentFiniteNormalization_moduleCechActualHigherHLinearEquiv A B D hR hS a ha c hc hgenR hgenC k q x =
      (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hR hS a ha c hc
        (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))) hgenR hgenC k q).hom x := rfl
end LinearStudy
