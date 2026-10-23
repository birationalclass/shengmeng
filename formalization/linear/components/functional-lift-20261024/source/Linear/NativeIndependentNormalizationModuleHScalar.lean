module
public import Linear.NativeIndependentNormalizationHFactorization
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
/-- The SAME original module-valued ambient-Cech/source-H comparison
intertwines actual base-scalar coefficient maps in every integer twist
and positive degree,using original module-homology forgetting. -/
theorem nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_baseScalar
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :
    let MA := nativeProjectiveModuleSheaf A D hR k
    let MB := nativeProjectiveModuleSheaf B D hS k
    let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
    let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
    let phiA := orderedBaseCechActualCoefficientMap piA
      (originalGlobalModuleScalar (piA.appTop r) MA) (fun i => Proj.basicOpen A (a i))
    let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop r) MB)
    (forget₂ (ModuleCat.{u} Γ(Spec (CommRingCat.of K),⊤)) AddCommGrpCat.{u}).map
        (HomologicalComplex.homologyMap phiA (q+1)) ≫
      (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hR hS a ha c hc piA hgenR hgenC k q).hom =
    (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hR hS a ha c hc piA hgenR hgenC k q).hom ≫
      (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map fB := by
  let MA := nativeProjectiveModuleSheaf A D hR k
  let MB := nativeProjectiveModuleSheaf B D hS k
  let U := fun i => Proj.basicOpen A (a i)
  let piA := Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let muA := originalGlobalModuleScalar (piA.appTop r) MA
  let fA := (schemeModuleToActualAbelianSheaf (Proj A)).map muA
  let fB := (schemeModuleToActualAbelianSheaf (Proj B)).map
    (originalGlobalModuleScalar (piB.appTop r) MB)
  let phiA := orderedBaseCechActualCoefficientMap piA muA U
  let mA := orderedTopAbelianCechCoefficientMap (Proj A) U fA
  let H := forget₂ (ModuleCat.{u} Γ(Spec (CommRingCat.of K),⊤)) AddCommGrpCat.{u}
  let E := orderedModuleCechActualAbelianHomologyIso piA MA U (q+1)
  let J := nativeIndependentFiniteNormalization_actualHigherHIso A B D hR hS a ha c hc hgenR hgenC k q
  have h1 : CommSq (H.map (HomologicalComplex.homologyMap phiA (q+1))) E.hom E.hom
      (HomologicalComplex.homologyMap mA (q+1)) :=
    ⟨orderedModuleCechActualAbelianHomologyIso_coefficient_naturality piA muA U (q+1)⟩
  have h2 : CommSq (HomologicalComplex.homologyMap mA (q+1)) J.hom J.hom
      ((CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map fB) :=
    ⟨nativeIndependentFiniteNormalization_actualHigherHIso_baseScalar A B D hR hS a ha c hc
      hgenR hgenC k q r⟩
  simp only [nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_factorization,Iso.trans_hom]
  exact (h1.vert_comp h2).w
end LinearStudy
