module
public import Linear.SchemeModuleActualSectionBoundaryLinear
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
/-- A nonzero ORIGINAL section-relation functional descends through the
SAME original ACTUAL boundary as a nonzero base-field-linear functional.
Actual exactness remains EXPLICIT in this generic transfer;the original
geometric Serre application will supply it. Quotient descent reuses
mathlib liftOfSurjective;no desired descended functional is input. -/
theorem schemeModuleOriginalActualSectionRelation_nonzero_descent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) {E M : X.Modules}
    (CC : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : CC ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (CC.X (r+1))) (phi : CC.X r ≅ M)
    (hExact : schemeModuleOriginalActualSectionExactStatement CC r alpha hAlpha hAbove phi) :
    letI : Module K Γ(E,⊤) := schemeModuleSectionsSpecModule pi E
    letI : Module K (schemeModuleActualCohomology X M r) := schemeModuleActualHSpecModule pi M r
    ∀ lambda : Module.Dual K Γ(E,⊤),lambda ≠ 0 →
      (∀ z : Γ(CC.X 0,⊤),lambda ((alpha.f 0).app ⊤ z)=0) →
      ∃ ell : Module.Dual K (schemeModuleActualCohomology X M r),ell ≠ 0 ∧
        ∀ s : Γ(E,⊤),ell (schemeModuleOriginalActualSectionBoundary CC r alpha hAlpha hAbove phi s)=lambda s := by
  dsimp only
  letI : Module K Γ(E,⊤) := schemeModuleSectionsSpecModule pi E
  letI : Module K (schemeModuleActualCohomology X M r) := schemeModuleActualHSpecModule pi M r
  intro lambda hne hrel
  let delta : Γ(E,⊤) →ₗ[K] schemeModuleActualCohomology X M r :=
    schemeModuleOriginalActualSectionBoundarySpecLinearMap pi CC r alpha hAlpha hAbove phi
  have hd : Function.Surjective delta := hExact.1
  have hker : delta.ker ≤ lambda.ker := by
    intro s hs
    have hs0 : schemeModuleOriginalActualSectionBoundary CC r alpha hAlpha hAbove phi s=0 := hs
    obtain ⟨z,hz⟩ := (hExact.2 s).mp hs0
    change lambda s=0
    rw [← hz]
    exact hrel z
  let ell : Module.Dual K (schemeModuleActualCohomology X M r) :=
    (delta.liftOfSurjective hd) ⟨lambda,hker⟩
  have hvalue (s : Γ(E,⊤)) : ell (schemeModuleOriginalActualSectionBoundary CC r alpha hAlpha hAbove phi s)=lambda s :=
    LinearMap.equivOfSurjective_apply (f:=delta) hd hker
  have hell : ell ≠ 0 := by
    intro hz
    apply hne
    apply LinearMap.ext
    intro s
    have h := (hvalue s).symm
    rw [hz] at h
    exact h
  exact ⟨ell,hell,hvalue⟩
end LinearStudy
