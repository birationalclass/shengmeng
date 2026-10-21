module
public import Linear.NativeIndependentSourceAmbientOrderedTwistCech
public import Linear.NativeIndependentSourceAmbientOrderedCechScalar
public import Linear.OrderedCechModuleScalarNaturality
public import Linear.NativeProjectiveTwistRegrading
public import Linear.NativeFiniteGradedSourceAmbientOrderedTwistCech
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
variable {κ : Type u} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
include c hc
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
open CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
/-- EVERY integer twist of the SAME old cross-space ordered Cech iso
intertwines ORIGINAL actual base-scalar coefficient maps. Regrading is
O-linear and its scalar squares are derived from native naturality. -/
theorem nativeIndependentSourceAmbientOrderedTwistCechIso_baseScalar
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :
    let MA := nativeProjectiveModuleSheaf A D hR k
    let MB := nativeProjectiveModuleSheaf B D hS k
    let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
    let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
    let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map
      (originalGlobalModuleScalar (piA.appTop r) MA)
    let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop r) MB)
    (nativeIndependentSourceAmbientOrderedTwistCechIso A B D hR hS a ha c hc hgenR hgenC k).hom ≫
      orderedTopAbelianCechCoefficientMap (Proj B) (fun i => Proj.basicOpen B (algebraMap R S (a i))) fB =
    orderedTopAbelianCechCoefficientMap (Proj A) (fun i => Proj.basicOpen A (a i)) fA ≫
      (nativeIndependentSourceAmbientOrderedTwistCechIso A B D hR hS a ha c hc hgenR hgenC k).hom := by
  let Dk := integerGradingShift D k
  let hRk := integerGradingShift_smul_homogeneous A D hR k
  let hSk := integerGradingShift_smul_homogeneous B D hS k
  letI : DirectSum.Decomposition Dk := integerGradingShiftDecomposition D k
  let U := fun i => Proj.basicOpen A (a i)
  let V := fun i => Proj.basicOpen B (algebraMap R S (a i))
  let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let eOA := nativeProjectiveTwistRegradingIso A D hR k
  let eOB := nativeProjectiveTwistRegradingIso B D hS k
  let eA := orderedTopAbelianCechCoefficientIso U ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso eOA)
  let eB := orderedTopAbelianCechCoefficientIso V ((schemeModuleToActualAbelianSheaf (Proj B)).mapIso eOB)
  let e := nativeIndependentSourceAmbientOrderedCechIso A B Dk hRk hSk a ha c hc hgenR hgenC
  let muAk := orderedTopAbelianCechCoefficientMap (Proj A) U
    ((schemeModuleToActualAbelianSheaf (Proj A)).map
      (originalGlobalModuleScalar (piA.appTop r) (nativeProjectiveModuleSheaf A D hR k)))
  let muA0 := orderedTopAbelianCechCoefficientMap (Proj A) U
    ((schemeModuleToActualAbelianSheaf (Proj A)).map
      (originalGlobalModuleScalar (piA.appTop r) (nativeProjectiveModuleSheaf A Dk hRk 0)))
  let muBk := orderedTopAbelianCechCoefficientMap (Proj B) V
    ((schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop r) (nativeProjectiveModuleSheaf B D hS k)))
  let muB0 := orderedTopAbelianCechCoefficientMap (Proj B) V
    ((schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop r) (nativeProjectiveModuleSheaf B Dk hSk 0)))
  have hA : CommSq muAk eA.inv eA.inv muA0 := by
    constructor
    change muAk ≫ (orderedTopAbelianCechCoefficientIso U
      ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso eOA)).inv = _
    rw [orderedTopAbelianCechCoefficientIso_inv_eq_map]
    exact (orderedTopAbelianCech_moduleScalar_naturality U (piA.appTop r) eOA.inv).symm
  have hB : CommSq muB0 eB.hom eB.hom muBk := by
    constructor
    change muB0 ≫ (orderedTopAbelianCechCoefficientIso V
      ((schemeModuleToActualAbelianSheaf (Proj B)).mapIso eOB)).hom = _
    rw [orderedTopAbelianCechCoefficientIso_hom_eq_map]
    exact (orderedTopAbelianCech_moduleScalar_naturality V (piB.appTop r) eOB.hom).symm
  have h0 : CommSq muA0 e.hom e.hom muB0 :=
    ⟨(nativeIndependentSourceAmbientOrderedCechIso_baseScalar A B Dk hRk hSk a ha c hc
      hgenR hgenC r).symm⟩
  change (eA.inv ≫ e.hom ≫ eB.hom) ≫ muBk = muAk ≫ (eA.inv ≫ e.hom ≫ eB.hom)
  exact (hA.vert_comp (h0.vert_comp hB)).w.symm
end LinearStudy
