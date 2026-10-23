module
public import Linear.NativeCoextensionSpecifiedTraceHomVanishing
public import Linear.NativeProjectiveShiftAtTwist
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [IsDomain S] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  coextensionGradedDecomposition coextensionOriginalBaseScalarTower
attribute [local instance] coextensionTraceBaseSourceTower coextensionTraceFieldSourceTower
  coextensionTraceFiniteBase coextensionTraceFiniteSource coextensionTraceTorsionFree
  schemeModuleActualCohomologyAddCommGroup
attribute [local irreducible] nativeFiniteNormalization_specifiedActualTopHomDualIso
variable {M : Type} [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M] [Module S M]
variable [IsScalarTower (MvPolynomial σ K) S M] [IsScalarTower K (MvPolynomial σ K) M] [IsScalarTower K S M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K n →
  ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable [Module.IsTorsionFree S M] [Module.Finite (MvPolynomial σ K) M] [Module.Finite S M]
attribute [local irreducible] nativeCoextensionSpecifiedTopEvaluationTrace integerGradedHomPrecomposition
  nativeProjectiveModuleSheaf nativeProjectiveDegreeZeroSheafMap
attribute [local instance] integerGradingShiftDecomposition
include hR in
/-- For EVERY ORIGINAL integer twist k,vanishing of actual sheaf morphisms
into the SAME constructed C(-card sigma) implies actual top-H vanishing.
The actual identity-on-local-values regrading isomorphism is reused.
No normalized geometric trace or canonical-module identification is input. -/
theorem nativeCoextensionSpecifiedTrace_actualTop_allTwists_vanish_of_hom_zero
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ)
    (hhom : ∀ a : nativeProjectiveModuleSheaf B D hS k ⟶
        nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
          (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
          (-(Fintype.card σ:ℤ)),a=0) :
    Subsingleton (schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B D hS k) (q+1)) := by
  let k0 : ℤ := -(Fintype.card σ:ℤ)
  let delta : ℤ := k-k0
  let DS := integerGradingShift D delta
  let hRS := integerGradingShift_smul_homogeneous
    (MvPolynomial.homogeneousSubmodule σ K) D hR delta
  let hSS := integerGradingShift_smul_homogeneous B D hS delta
  have hk : k0+delta=k := by dsimp only [delta];omega
  let e : nativeProjectiveModuleSheaf B DS hSS k0 ≅
      nativeProjectiveModuleSheaf B D hS k :=
    nativeProjectiveShiftAtTwistIso B D hS delta k0 ≪≫
      eqToIso (congrArg (nativeProjectiveModuleSheaf B D hS) hk)
  have hhomS : ∀ a : nativeProjectiveModuleSheaf B DS hSS k0 ⟶
      nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
        (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) k0,
      a=0 := by
    intro a
    have h := hhom (e.inv ≫ a)
    calc
      a = e.hom ≫ (e.inv ≫ a) := by
        simp only [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
      _ = 0 := by rw [h,comp_zero]
  have hs : Subsingleton (schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B DS hSS k0) (q+1)) :=
    nativeCoextensionSpecifiedTrace_actualTop_vanish_of_hom_zero
      B DS hRS hSS c hc hgenC q hcard hhomS
  let eH := (CategoryTheory.Sheaf.functorH
    (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).mapIso
      ((schemeModuleToActualAbelianSheaf (Proj B)).mapIso e)
  exact eH.addCommGroupIsoToAddEquiv.subsingleton_congr.mp hs
end LinearStudy
