module
public import Mathlib.Algebra.Module.LocalizedModule.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
/-- Function-level localization square. Only denominator-scalar compatibility
is needed; neither q nor theta0 nor theta1 must be packaged as a linear map.
This avoids adding source-localization or torsion-free hypotheses.
Verification status is recorded separately in exact compile/audit evidence. -/
theorem localizedSectionFunction_surjective
    {R T P N M : Type*} [CommSemiring R]
    (S : Submonoid R)
    [AddCommMonoid T] [Module R T] [AddCommMonoid P] [Module R P]
    [SMul R N]
    (psi : T →ₗ[R] P) [IsLocalizedModule S psi]
    (q : M → N) (theta0 : M → T) (theta1 : N → P)
    (hdivide : ∀ s : S, Function.Surjective (fun y : N => (s : R) • y))
    (hscalar : ∀ (s : S) (y : N), theta1 ((s : R) • y) = (s : R) • theta1 y)
    (h0 : Function.Surjective theta0)
    (hcomm : ∀ x, theta1 (q x) = psi (theta0 x)) :
    Function.Surjective theta1 := by
  intro z
  obtain ⟨⟨r,s⟩,hs⟩ := IsLocalizedModule.surj S psi z
  obtain ⟨x,hx⟩ := h0 r
  obtain ⟨y,hy⟩ := hdivide s (q x)
  change (s : R) • y = q x at hy
  refine ⟨y,?_⟩
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units psi s)).1
  change (s : R) • theta1 y = (s : R) • z
  rw [← hscalar s y,hy,hcomm,hx]
  exact hs.symm
end LinearStudy
