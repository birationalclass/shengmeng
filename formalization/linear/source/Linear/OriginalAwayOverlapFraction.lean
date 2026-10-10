module
public import Linear.LocalizedModuleAwayOverlapFraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
variable {R : Type*} [CommRing R]

/-- mathlib's ACTUAL coordinate-overlap ring restriction keeps the original
fraction by multiplying numerator and denominator by the same b^n. -/
theorem originalAwayOverlap_mk (a b z : R) (n : ℕ) :
    (IsLocalization.Away.awayToAwayRight a b :
      Localization.Away a →+* Localization.Away (a*b))
      (IsLocalization.mk' (Localization.Away a) z
        (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)) =
      IsLocalization.mk' (Localization.Away (a*b)) (b^n*z)
        (⟨(a*b)^n,⟨n,rfl⟩⟩ : Submonoid.powers (a*b)) := by
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  change (IsLocalization.Away.awayToAwayRight a b :
      Localization.Away a →+* Localization.Away (a*b))
      (IsLocalization.mk' (Localization.Away a) z
        (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)) *
      algebraMap R (Localization.Away (a*b)) ((a*b)^n) =
      algebraMap R (Localization.Away (a*b)) (b^n*z)
  rw [mul_pow,map_mul,← mul_assoc,
    ← IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away a)
      (P := Localization.Away (a*b)) a b (a^n),
    ← map_mul,IsLocalization.mk'_spec,
    IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away a)
      (P := Localization.Away (a*b)),← map_mul,mul_comm z (b^n)]

end LinearStudy
