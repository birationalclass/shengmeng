module
public import Linear.ModuleBaseSourceLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u
variable {R S M N : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
/-- The ORIGINAL base/source localization comparison is natural for an
ORIGINAL S-linear coefficient map,restricted to R on the ambient side.
Both actual localization maps retain the SAME original numerator. -/
theorem moduleBaseSourceLocalizationEquiv_map (a : R) (f : M →ₗ[S] N)
    (x : LocalizedModule (Submonoid.powers a) M) :
    LocalizedModule.map (Submonoid.powers (algebraMap R S a)) f
      (moduleBaseSourceLocalizationEquiv (S:=S) a x) =
      moduleBaseSourceLocalizationEquiv (S:=S) a
        (LocalizedModule.map (Submonoid.powers a) (f.restrictScalars R) x) := by
  induction x using LocalizedModule.induction_on with
  | h m b =>
    simp only [moduleBaseSourceLocalizationEquiv_mk,LocalizedModule.map_mk,
      LinearMap.restrictScalars_apply]
end LinearStudy
