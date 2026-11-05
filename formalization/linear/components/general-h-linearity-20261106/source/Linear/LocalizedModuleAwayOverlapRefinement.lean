module
public import Linear.LocalizedModuleAwayOverlapFraction
public import Linear.LocalizedModuleRefinementComposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Any original denominator set inverting both coordinates also inverts
their product. This includes a common prime-complement localization. -/
theorem originalAwayOverlap_powers_le (a b : R) (T : Submonoid R)
    (ha : Submonoid.powers a ≤ T) (hb : Submonoid.powers b ≤ T) :
    Submonoid.powers (a*b) ≤ T := by
  apply Submonoid.powers_le.mpr
  exact T.mul_mem (ha (Submonoid.mem_powers a)) (hb (Submonoid.mem_powers b))

/-- Restricting through an actual coordinate overlap agrees with direct
restriction to the same original localization. No false inclusion of
the powers of a into the powers of a*b is used. -/
theorem originalLocalizedModuleAwayOverlap_refinement
    (a b : R) (T : Submonoid R)
    (ha : Submonoid.powers a ≤ T) (hb : Submonoid.powers b ≤ T)
    (x : LocalizedModule (Submonoid.powers a) M) :
    originalLocalizedModuleRefinement (Submonoid.powers (a*b)) T
      (originalAwayOverlap_powers_le a b T ha hb)
      (originalLocalizedModuleAwayOverlap a b x) =
    originalLocalizedModuleRefinement (Submonoid.powers a) T ha x := by
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨k,hk⟩ := s.property
    have hs : s = (⟨a^k,⟨k,rfl⟩⟩ : Submonoid.powers a) := Subtype.ext hk.symm
    subst s
    rw [originalLocalizedModuleAwayOverlap_mk,
      originalLocalizedModuleRefinement_mk,originalLocalizedModuleRefinement_mk]
    have hd : (⟨(a*b)^k,originalAwayOverlap_powers_le a b T ha hb ⟨k,rfl⟩⟩ : T) =
        (⟨b^k,hb ⟨k,rfl⟩⟩ : T) * (⟨a^k,ha ⟨k,rfl⟩⟩ : T) := by
      apply Subtype.ext
      simp only [Submonoid.coe_mul,mul_pow,mul_comm]
    rw [hd]
    simpa only [Submonoid.smul_def] using
      LocalizedModule.mk_cancel_common_left (⟨b^k,hb ⟨k,rfl⟩⟩ : T)
        (⟨a^k,ha ⟨k,rfl⟩⟩ : T) m
end LinearStudy
