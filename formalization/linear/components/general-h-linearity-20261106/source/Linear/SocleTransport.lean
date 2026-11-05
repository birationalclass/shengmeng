module
public import Linear.SoclePairing
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {C D : Type*} [CommRing C] [CommRing D] [IsLocalRing C] [IsLocalRing D]

theorem ringEquiv_socle_forward (e : C ≃+* D) (a : C)
    (ha : a ∈ (IsLocalRing.maximalIdeal C).annihilator) :
    e a ∈ (IsLocalRing.maximalIdeal D).annihilator := by
  apply Submodule.mem_annihilator.mpr
  intro v hv
  obtain ⟨u, rfl⟩ := e.surjective v
  have hu : u ∈ IsLocalRing.maximalIdeal C := by
    change ¬ IsUnit u
    change ¬ IsUnit (e u) at hv
    exact fun h => hv (h.map e.toMonoidHom)
  have h := Submodule.mem_annihilator.mp ha u hu
  change a * u = 0 at h
  change e a * e u = 0
  simpa only [map_mul, map_zero] using congrArg e h

theorem ringEquiv_socle_iff (e : C ≃+* D) (a : C) :
    a ∈ (IsLocalRing.maximalIdeal C).annihilator ↔
      e a ∈ (IsLocalRing.maximalIdeal D).annihilator := by
  constructor
  · exact ringEquiv_socle_forward e a
  · intro ha
    simpa only [e.symm_apply_apply] using ringEquiv_socle_forward e.symm (e a) ha

theorem scalar_socle_transport {k K : Type*} [Field k] [Field K]
    [Algebra k C] [Algebra K D] (e : C ≃+* D) (ef : k ≃+* K)
    (hscalar : ∀ u a, e (u • a) = ef u • e a) (delta : D)
    (hsoc : ∀ a : D, a ∈ (IsLocalRing.maximalIdeal D).annihilator →
      ∃ u : K, a = u • delta) :
    ∀ a : C, a ∈ (IsLocalRing.maximalIdeal C).annihilator →
      ∃ u : k, a = u • e.symm delta := by
  intro a ha
  obtain ⟨u, hu⟩ := hsoc (e a) (ringEquiv_socle_forward e a ha)
  refine ⟨ef.symm u, e.injective ?_⟩
  rw [hscalar, ef.apply_symm_apply, e.apply_symm_apply]
  exact hu

end LinearStudy
