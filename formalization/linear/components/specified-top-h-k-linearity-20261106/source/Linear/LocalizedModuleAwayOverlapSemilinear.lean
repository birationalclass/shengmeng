module
public import Linear.OriginalAwayOverlapFraction
public import Linear.NativeLocalizationScalarComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The actual coordinate-overlap module restriction is semilinear for
the ACTUAL away-to-away ring map, not only linear over the original R. -/
theorem originalLocalizedModuleAwayOverlap_smul
    (a b : R) (c : Localization.Away a)
    (x : LocalizedModule (Submonoid.powers a) M) :
    originalLocalizedModuleAwayOverlap a b (c • x) =
      (IsLocalization.Away.awayToAwayRight a b :
        Localization.Away a →+* Localization.Away (a*b)) c •
        originalLocalizedModuleAwayOverlap a b x := by
  obtain ⟨⟨r,s⟩,hc⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) c
  dsimp only at hc
  rw [← hc]
  induction x using LocalizedModule.induction_on with
  | _ m t =>
    obtain ⟨n,hn⟩ := s.property
    obtain ⟨k,hk⟩ := t.property
    have hs : s = (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) := Subtype.ext hn.symm
    have ht : t = (⟨a^k,⟨k,rfl⟩⟩ : Submonoid.powers a) := Subtype.ext hk.symm
    subst s t
    have hd : (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) * ⟨a^k,⟨k,rfl⟩⟩ =
        ⟨a^(n+k),⟨n+k,rfl⟩⟩ := by
      apply Subtype.ext
      simp only [Submonoid.coe_mul,pow_add]
    have hd' : (⟨(a*b)^n,⟨n,rfl⟩⟩ : Submonoid.powers (a*b)) * ⟨(a*b)^k,⟨k,rfl⟩⟩ =
        ⟨(a*b)^(n+k),⟨n+k,rfl⟩⟩ := by
      apply Subtype.ext
      simp only [Submonoid.coe_mul,pow_add]
    rw [← localizedModule_abstract_smul_eq_native (Submonoid.powers a)]
    rw [LocalizedModule.mk'_smul_mk (Localization.Away a) r m
      (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) (⟨a^k,⟨k,rfl⟩⟩ : Submonoid.powers a),hd,originalLocalizedModuleAwayOverlap_mk,
      originalAwayOverlap_mk,originalLocalizedModuleAwayOverlap_mk]
    rw [← localizedModule_abstract_smul_eq_native (Submonoid.powers (a*b)),
      LocalizedModule.mk'_smul_mk (Localization.Away (a*b)) (b^n*r) (b^k • m)
        (⟨(a*b)^n,⟨n,rfl⟩⟩ : Submonoid.powers (a*b))
        (⟨(a*b)^k,⟨k,rfl⟩⟩ : Submonoid.powers (a*b)),hd']
    congr 1
    simp only [smul_smul,pow_add,mul_assoc,mul_left_comm,mul_comm]

/-- Bundle the already constructed actual restriction with its proved
scalar law. This is the map needed by actual chart-module gluing. -/
def originalLocalizedModuleAwayOverlapSemilinear (a b : R) :
    LocalizedModule (Submonoid.powers a) M
      →ₛₗ[(IsLocalization.Away.awayToAwayRight a b :
        Localization.Away a →+* Localization.Away (a*b))]
        LocalizedModule (Submonoid.powers (a*b)) M where
  toFun := originalLocalizedModuleAwayOverlap a b
  map_add' := (originalLocalizedModuleAwayOverlap a b).map_add
  map_smul' := originalLocalizedModuleAwayOverlap_smul a b

end LinearStudy
