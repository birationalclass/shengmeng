module
public import Linear.NativeIndependentNormalizationActualHComparison
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
/-- The SAME module-valued ambient Cech homology computes actual H of
the finite-normalization source after EXACT scalar forgetting. This is the
actual complex used by polynomial coefficient duality,not a new model. -/
def nativeIndependentFiniteNormalization_moduleCechActualHigherHIso
    {Y : Scheme.{u}} (pi : Proj A ⟶ Y)
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(Y,⊤)) AddCommGrpCat.{u}).obj
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex pi
        (nativeProjectiveModuleSheaf A D hR k)
        (fun i => Proj.basicOpen A (a i))).homology (q+1)) ≅
      AddCommGrpCat.of (schemeModuleActualCohomology (Proj B)
        (nativeProjectiveModuleSheaf B D hS k) (q+1)) := by
  let H := forget₂ (ModuleCat.{u} Γ(Y,⊤)) AddCommGrpCat.{u}
  let C := AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex pi
    (nativeProjectiveModuleSheaf A D hR k) (fun i => Proj.basicOpen A (a i))
  exact ((C.sc (q+1)).mapHomologyIso H).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (q+1)).mapIso
      (orderedModuleCechActualAbelianComplexIso pi (nativeProjectiveModuleSheaf A D hR k)
        (fun i => Proj.basicOpen A (a i))) ≪≫
      nativeIndependentFiniteNormalization_actualHigherHIso A B D hR hS a ha c hc hgenR hgenC k q
end LinearStudy
