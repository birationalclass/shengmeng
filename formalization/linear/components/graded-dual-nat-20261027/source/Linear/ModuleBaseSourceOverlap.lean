module
public import Linear.ModuleBaseSourceLocalization
public import Linear.LocalizedModuleAwayOverlapFraction
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

theorem moduleBaseSourceLocalizationEquiv_mk_pow (a : R) (m : M) (n : ℕ) :
    moduleBaseSourceLocalizationEquiv (S := S) a
      (LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)) =
      LocalizedModule.mk m
        (⟨(algebraMap R S a)^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S a)) := by
  rw [moduleBaseSourceLocalizationEquiv_mk]
  congr 1
  apply Subtype.ext
  exact map_pow (algebraMap R S) a n

/-- The actual source overlap restriction with its denominator expressed
as the image of the ORIGINAL product coordinate. The original numerator
map and invertible-denominator action define this restriction. -/
def sourceModuleBaseCoordinateOverlap (a b : R) :
    LocalizedModule (Submonoid.powers (algebraMap R S a)) M →ₗ[S]
      LocalizedModule (Submonoid.powers (algebraMap R S (a*b))) M :=
  LocalizedModule.lift (Submonoid.powers (algebraMap R S a))
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (a*b))) M)
    (by intro s; rw [map_mul];
        exact originalLocalizedModuleAwayOverlap_unit (M := M) (algebraMap R S a) (algebraMap R S b) s)

theorem sourceModuleBaseCoordinateOverlap_mk (a b : R) (m : M) (n : ℕ) :
    sourceModuleBaseCoordinateOverlap (S := S) a b
      (LocalizedModule.mk m
        (⟨(algebraMap R S a)^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S a))) =
      LocalizedModule.mk ((algebraMap R S b)^n • m)
        (⟨(algebraMap R S (a*b))^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S (a*b))) := by
  have hu : IsUnit (algebraMap S (Module.End S
      (LocalizedModule (Submonoid.powers (algebraMap R S (a*b))) M)) ((algebraMap R S a)^n)) := by
    rw [map_mul]
    exact originalLocalizedModuleAwayOverlap_unit (M := M) (algebraMap R S a) (algebraMap R S b)
      (⟨(algebraMap R S a)^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S a))
  apply ((Module.End.isUnit_iff _).mp hu).1
  change (algebraMap R S a)^n • sourceModuleBaseCoordinateOverlap (S := S) a b
      (LocalizedModule.mk m
        (⟨(algebraMap R S a)^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S a))) =
      (algebraMap R S a)^n • LocalizedModule.mk ((algebraMap R S b)^n • m)
        (⟨(algebraMap R S (a*b))^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S (a*b)))
  rw [← (sourceModuleBaseCoordinateOverlap (M := M) (S := S) a b).map_smul]
  have hcan : (algebraMap R S a)^n • LocalizedModule.mk m
      (⟨(algebraMap R S a)^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S a)) =
      LocalizedModule.mk m 1 := by
    simpa only [LocalizedModule.smul'_mk,Submonoid.smul_def] using
      LocalizedModule.mk_cancel (⟨(algebraMap R S a)^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S a)) m
  rw [hcan]
  have hcan' : (algebraMap R S a)^n • LocalizedModule.mk ((algebraMap R S b)^n • m)
      (⟨(algebraMap R S (a*b))^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S (a*b))) =
      LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk,smul_smul,← mul_pow,← map_mul]
    exact LocalizedModule.mk_cancel
      (⟨(algebraMap R S (a*b))^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S (a*b))) m
  rw [hcan']
  exact LocalizedModule.lift_mk_one _ _ _ m

/-- Universal base/source localization comparison commutes with the
ACTUAL original chart-overlap restriction. Neither an overlap model nor
compatibility certificate is supplied. -/
theorem moduleBaseSourceLocalizationEquiv_overlap (a b : R)
    (x : LocalizedModule (Submonoid.powers a) M) :
    moduleBaseSourceLocalizationEquiv (S := S) (a*b)
      (originalLocalizedModuleAwayOverlap a b x) =
      sourceModuleBaseCoordinateOverlap (S := S) a b
        (moduleBaseSourceLocalizationEquiv (S := S) a x) := by
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨n,hn⟩ := s.property
    have hs : s = (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) := Subtype.ext hn.symm
    subst s
    rw [originalLocalizedModuleAwayOverlap_mk,moduleBaseSourceLocalizationEquiv_mk_pow,
      moduleBaseSourceLocalizationEquiv_mk_pow,sourceModuleBaseCoordinateOverlap_mk]
    congr 1
    rw [← map_pow]
    exact (IsScalarTower.algebraMap_smul S (b^n) m).symm
end LinearStudy
