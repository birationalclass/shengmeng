module
public import Linear.NativeIndependentNormalizationActualHFactorization
public import Linear.NativeIndependentSourceAmbientOrderedTwistCechScalar
public import Linear.NativeProjActualHCoefficientNaturality
public import Linear.NativeProjectiveTwistQuasicoherent
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
attribute [local irreducible] finiteTypeNativeProj_orderedActualHigherHIso
  noetherianFiniteOrderedAffineCover_actualHigherHIso topFiniteOrderedCech_actualHigherHIso_of_localAcyclic
  nativeIndependentSourceAmbientOrderedTwistCechIso orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso
set_option diagnostics true
set_option diagnostics.threshold 1000
/-- The SAME existing finite-normalization ambient-Cech/actual-source-H
comparison intertwines ORIGINAL base-global scalar coefficient maps in
EVERY integer twist and EVERY positive degree. Source QC,Noetherianity,
cover,affine intersections and local H vanishing are DERIVED. -/
theorem nativeIndependentFiniteNormalization_actualHigherHIso_baseScalar
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :
    let MA : (Proj A).Modules := nativeProjectiveModuleSheaf A D hR k
    let MB : (Proj B).Modules := nativeProjectiveModuleSheaf B D hS k
    let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
    let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
    let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map
      (originalGlobalModuleScalar (piA.appTop r) MA)
    let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop r) MB)
    HomologicalComplex.homologyMap
        (orderedTopAbelianCechCoefficientMap (Proj A) (fun i => Proj.basicOpen A (a i)) fA) (q+1) ≫
      (nativeIndependentFiniteNormalization_actualHigherHIso A B D hR hS a ha c hc hgenR hgenC k q).hom =
    (nativeIndependentFiniteNormalization_actualHigherHIso A B D hR hS a ha c hc hgenR hgenC k q).hom ≫
      (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map fB := by
  let MA : (Proj A).Modules := nativeProjectiveModuleSheaf A D hR k
  let MB : (Proj B).Modules := nativeProjectiveModuleSheaf B D hS k
  letI : MB.IsQuasicoherent := nativeFiniteGradedTwist_isQuasicoherent_of_cover B D hS k c hc
    (degreeOneGenerated_nativeProj_cover B c hc hgenC)
  trace "SCALAR_AFTER_QC"
  let U := fun i => Proj.basicOpen A (a i)
  let V := fun i => Proj.basicOpen B (algebraMap R S (a i))
  let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map
    (originalGlobalModuleScalar (piA.appTop r) MA)
  let fB0 := originalGlobalModuleScalar (piB.appTop r) MB
  let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map fB0
  let mA := orderedTopAbelianCechCoefficientMap (Proj A) U fA
  let mB := orderedTopAbelianCechCoefficientMap (Proj B) V fB
  let E := nativeIndependentSourceAmbientOrderedTwistCechIso A B D hR hS a ha c hc hgenR hgenC k
  let J := finiteTypeNativeProj_orderedActualHigherHIso B (fun i => algebraMap R S (a i))
    (fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i))
    (nativeFiniteNormalization_sourceCoordinateCover A B a ha hgenR) MB q
  trace "SCALAR_AFTER_NATIVE_COMPARISON"
  let T := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) (q+1)
  have hE : CommSq mA E.hom E.hom mB :=
    ⟨(nativeIndependentSourceAmbientOrderedTwistCechIso_baseScalar A B D hR hS a ha c hc
      hgenR hgenC k r).symm⟩
  trace "SCALAR_AFTER_CECH_SQUARE"
  have h1 := T.map_commSq hE
  trace "SCALAR_AFTER_HOMOLOGY_SQUARE"
  have h2 : CommSq (HomologicalComplex.homologyMap mB (q+1)) J.hom J.hom
      ((CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map fB) :=
    ⟨finiteTypeNativeProj_orderedActualHigherHIso_coefficient_naturality B
      (fun i => algebraMap R S (a i))
      (fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i))
      (nativeFiniteNormalization_sourceCoordinateCover A B a ha hgenR) fB0 q⟩
  trace "SCALAR_AFTER_ACTUAL_H_SQUARE"
  simp only [nativeIndependentFiniteNormalization_actualHigherHIso_factorization,Iso.trans_hom]
  exact (h1.vert_comp h2).w
end LinearStudy
