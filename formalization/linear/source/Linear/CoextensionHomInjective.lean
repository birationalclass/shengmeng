module
public import Linear.CoextensionIntegralEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u

/-- A module already embedded in a domain has rank at most one;
every nonzero map from it to that domain is injective. -/
theorem embeddedDomainModule_nonzero_map_injective
    {S D : Type*} [CommRing S] [IsDomain S] [AddCommGroup D] [Module S D]
    (e : D →ₗ[S] S) (he : Function.Injective e)
    (f : D →ₗ[S] S) (hf : f ≠ 0) : Function.Injective f := by
  classical
  have hn : ∃ x : D, f x ≠ 0 := by
    by_contra h
    apply hf
    ext x
    have h0 : ∀ y : D, f y = 0 := by simpa only [not_exists,not_not] using h
    exact h0 x
  obtain ⟨x,hx⟩ := hn
  intro y z hyz
  have hrel : e (y-z) • x = e x • (y-z) := by
    apply he
    simp only [map_smul,smul_eq_mul,mul_comm]
  have hfzero : f (y-z) = 0 := by rw [map_sub,hyz,sub_self]
  have hezero : e (y-z) = 0 := by
    have h := congrArg f hrel
    simp only [map_smul,smul_eq_mul,hfzero,mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hx
  have hyz' : y-z = 0 := he (hezero.trans (map_zero e).symm)
  exact sub_eq_zero.mp hyz'

/-- For the ACTUAL normalization dual, any nonzero upper-ring
linear map to the original upper ring is injective. Its rank-one
embedding is constructed by the actual fraction-field proof. -/
theorem coextensionDual_nonzero_linear_map_injective
    {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    (f : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) →ₗ[S] S)
    (hf : f ≠ 0) : Function.Injective f := by
  obtain ⟨e,he⟩ := coextensionDual_exists_integral_embedding (R := R) (S := S)
  exact embeddedDomainModule_nonzero_map_injective e he f hf

end LinearStudy
