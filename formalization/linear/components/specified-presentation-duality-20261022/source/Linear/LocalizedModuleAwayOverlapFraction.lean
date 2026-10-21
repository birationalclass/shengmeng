module
public import Linear.LocalizedModuleAwayOverlap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- On an actual coordinate overlap the original fraction m/a^n restricts
to b^n*m/(a*b)^n. This formula is proved in the actual localized module. -/
theorem originalLocalizedModuleAwayOverlap_mk (a b : R) (m : M) (n : ℕ) :
    originalLocalizedModuleAwayOverlap a b
      (LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)) =
      LocalizedModule.mk (b^n • m)
        (⟨(a*b)^n,⟨n,rfl⟩⟩ : Submonoid.powers (a*b)) := by
  have hu := originalLocalizedModuleAwayOverlap_unit (M := M) a b
    (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)
  have hi : Function.Injective
      (fun x : LocalizedModule (Submonoid.powers (a*b)) M => a^n • x) :=
    ((Module.End.isUnit_iff _).mp hu).1
  have hleft : a^n • LocalizedModule.mk m
      (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) = LocalizedModule.mk m 1 := by
    simpa only [LocalizedModule.smul'_mk,Submonoid.smul_def] using
      LocalizedModule.mk_cancel (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) m
  have hright : a^n • LocalizedModule.mk (b^n • m)
      (⟨(a*b)^n,⟨n,rfl⟩⟩ : Submonoid.powers (a*b)) =
      LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk,smul_smul,← mul_pow]
    exact LocalizedModule.mk_cancel (⟨(a*b)^n,⟨n,rfl⟩⟩ : Submonoid.powers (a*b)) m
  apply hi
  change a^n • originalLocalizedModuleAwayOverlap a b
      (LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)) =
      a^n • LocalizedModule.mk (b^n • m)
        (⟨(a*b)^n,⟨n,rfl⟩⟩ : Submonoid.powers (a*b))
  rw [← (originalLocalizedModuleAwayOverlap (M := M) a b).map_smul,hleft,
    originalLocalizedModuleAwayOverlap_mk_one,hright]

end LinearStudy
