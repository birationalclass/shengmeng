module
public import Mathlib.RingTheory.Localization.Module
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

/-- Actual localization at a base coordinate is equivalent to actual
localization at its image in the upper ring. This is the exact universal
comparison on the original module, with restricted base scalars. -/
def moduleBaseSourceLocalizationEquiv (a : R) :
    let Q := Submonoid.powers (algebraMap R S a)
    let N := LocalizedModule Q M
    LocalizedModule (Submonoid.powers a) M ≃ₗ[R] N := by
  let Q := Submonoid.powers (algebraMap R S a)
  let N := LocalizedModule Q M
  let j := (LocalizedModule.mkLinearMap Q M).restrictScalars R
  letI : IsLocalizedModule (Submonoid.powers a) j :=
    IsLocalizedModule.restrictScalars_powers a (LocalizedModule.mkLinearMap Q M)
  exact IsLocalizedModule.iso (Submonoid.powers a) j

/-- The universal comparison retains the original numerator. -/
theorem moduleBaseSourceLocalizationEquiv_mk_one (a : R) (m : M) :
    moduleBaseSourceLocalizationEquiv (S := S) a (LocalizedModule.mk m 1) =
      LocalizedModule.mk m 1 := by
  letI := IsLocalizedModule.restrictScalars_powers a
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S a)) M)
  exact IsLocalizedModule.iso_mk_one (Submonoid.powers a)
    ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S a)) M).restrictScalars R) m

/-- Its exact fraction formula uses the image of the ORIGINAL base
denominator. No arbitrary choice of comparison equivalence is allowed. -/
theorem moduleBaseSourceLocalizationEquiv_mk
    (a : R) (m : M) (b : Submonoid.powers a) :
    moduleBaseSourceLocalizationEquiv (S := S) a (LocalizedModule.mk m b) =
      LocalizedModule.mk m
        (⟨algebraMap R S b, by
          obtain ⟨n,hn⟩ := b.property
          exact ⟨n,by simpa only [map_pow] using congrArg (algebraMap R S) hn⟩⟩ :
          Submonoid.powers (algebraMap R S a)) := by
  let Q := Submonoid.powers (algebraMap R S a)
  let N := LocalizedModule Q M
  let b' : Q := ⟨algebraMap R S b,by
    obtain ⟨n,hn⟩ := b.property
    exact ⟨n,by simpa only [map_pow] using congrArg (algebraMap R S) hn⟩⟩
  let j := (LocalizedModule.mkLinearMap Q M).restrictScalars R
  letI : IsLocalizedModule (Submonoid.powers a) j :=
    IsLocalizedModule.restrictScalars_powers a (LocalizedModule.mkLinearMap Q M)
  have hb : Function.Injective (fun x : N => (b : R) • x) :=
    ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units j b)).1
  apply hb
  change (b : R) • (moduleBaseSourceLocalizationEquiv (S := S) a (LocalizedModule.mk m b)) =
    (b : R) • (LocalizedModule.mk m b' : N)
  rw [← (moduleBaseSourceLocalizationEquiv (S := S) a).map_smul]
  have hcancel : (b : R) • LocalizedModule.mk m b = LocalizedModule.mk m 1 := by
    simpa only [LocalizedModule.smul'_mk,Submonoid.smul_def] using LocalizedModule.mk_cancel b m
  rw [hcancel,moduleBaseSourceLocalizationEquiv_mk_one]
  rw [← IsScalarTower.algebraMap_smul S (b : R) (LocalizedModule.mk m b' : N)]
  symm
  simpa only [LocalizedModule.smul'_mk,Submonoid.smul_def] using LocalizedModule.mk_cancel b' m

end LinearStudy
