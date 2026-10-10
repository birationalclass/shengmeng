module
public import Linear.ModuleBaseSourceOverlap
public import Linear.LocalizedModuleAwayOverlapRefinement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
universe u
variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

theorem sourceBaseCoordinateOverlap_powers_le (a b : R) (T : Submonoid S)
    (ha : Submonoid.powers (algebraMap R S a) ≤ T)
    (hb : Submonoid.powers (algebraMap R S b) ≤ T) :
    Submonoid.powers (algebraMap R S (a*b)) ≤ T := by
  rw [map_mul]
  exact originalAwayOverlap_powers_le _ _ T ha hb

/-- Refining the actual source overlap to a common original localization
equals direct refinement; no compatibility certificate is an input. -/
theorem sourceModuleBaseCoordinateOverlap_refinement (a b : R) (T : Submonoid S)
    (ha : Submonoid.powers (algebraMap R S a) ≤ T)
    (hb : Submonoid.powers (algebraMap R S b) ≤ T)
    (x : LocalizedModule (Submonoid.powers (algebraMap R S a)) M) :
    originalLocalizedModuleRefinement (Submonoid.powers (algebraMap R S (a*b))) T
      (sourceBaseCoordinateOverlap_powers_le a b T ha hb)
      (sourceModuleBaseCoordinateOverlap (S := S) a b x) =
      originalLocalizedModuleRefinement (Submonoid.powers (algebraMap R S a)) T ha x := by
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨n,hn⟩ := s.property
    have hs : s = (⟨(algebraMap R S a)^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S a)) :=
      Subtype.ext hn.symm
    subst s
    rw [sourceModuleBaseCoordinateOverlap_mk,
      originalLocalizedModuleRefinement_mk,originalLocalizedModuleRefinement_mk]
    have hd : (⟨(algebraMap R S (a*b))^n,
        sourceBaseCoordinateOverlap_powers_le a b T ha hb ⟨n,rfl⟩⟩ : T) =
        (⟨(algebraMap R S b)^n,hb ⟨n,rfl⟩⟩ : T) *
        (⟨(algebraMap R S a)^n,ha ⟨n,rfl⟩⟩ : T) := by
      apply Subtype.ext
      simp only [Submonoid.coe_mul,map_mul,mul_pow,mul_comm]
    rw [hd]
    simpa only [Submonoid.smul_def] using LocalizedModule.mk_cancel_common_left
      (⟨(algebraMap R S b)^n,hb ⟨n,rfl⟩⟩ : T)
      (⟨(algebraMap R S a)^n,ha ⟨n,rfl⟩⟩ : T) m

/-- Both base/source comparison and original overlap restriction agree
after passage to the SAME common original source localization. -/
theorem moduleBaseSourceLocalizationEquiv_overlap_refinement (a b : R) (T : Submonoid S)
    (ha : Submonoid.powers (algebraMap R S a) ≤ T)
    (hb : Submonoid.powers (algebraMap R S b) ≤ T)
    (x : LocalizedModule (Submonoid.powers a) M) :
    originalLocalizedModuleRefinement (Submonoid.powers (algebraMap R S (a*b))) T
      (sourceBaseCoordinateOverlap_powers_le a b T ha hb)
      (moduleBaseSourceLocalizationEquiv (S := S) (a*b) (originalLocalizedModuleAwayOverlap a b x)) =
      originalLocalizedModuleRefinement (Submonoid.powers (algebraMap R S a)) T ha
        (moduleBaseSourceLocalizationEquiv (S := S) a x) := by
  rw [moduleBaseSourceLocalizationEquiv_overlap]
  exact sourceModuleBaseCoordinateOverlap_refinement a b T ha hb
    (moduleBaseSourceLocalizationEquiv (S := S) a x)
end LinearStudy
