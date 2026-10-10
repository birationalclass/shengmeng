module
public import Linear.LocalizedModuleRefinement
public import Mathlib.RingTheory.Localization.Away.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The original coordinate a is invertible on the ACTUAL overlap D(a*b),
including its action on the actual localized module. -/
theorem originalLocalizedModuleAwayOverlap_unit (a b : R) (s : Submonoid.powers a) :
    IsUnit (algebraMap R (Module.End R
      (LocalizedModule (Submonoid.powers (a*b)) M)) (s : R)) := by
  let Q := Localization.Away (a*b)
  have ha : IsUnit (algebraMap R Q a) :=
    IsLocalization.Away.isUnit_of_dvd (a*b) (dvd_mul_right a b)
  have hs : IsUnit (algebraMap R Q (s : R)) := by
    obtain ⟨n,hn⟩ := s.property
    rw [← hn,map_pow]
    exact ha.pow n
  rw [← (Algebra.lsmul R (A := Q) R
    (LocalizedModule (Submonoid.powers (a*b)) M)).commutes]
  exact hs.map (Algebra.lsmul R (A := Q) R
    (LocalizedModule (Submonoid.powers (a*b)) M)).toRingHom

/-- Actual module restriction from D(a) to D(a*b), constructed from
the universal property. No erroneous powers(a) ⊆ powers(a*b) is assumed. -/
def originalLocalizedModuleAwayOverlap (a b : R) :
    LocalizedModule (Submonoid.powers a) M →ₗ[R]
      LocalizedModule (Submonoid.powers (a*b)) M :=
  LocalizedModule.lift (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers (a*b)) M)
    (originalLocalizedModuleAwayOverlap_unit (M := M) a b)

theorem originalLocalizedModuleAwayOverlap_mk_one (a b : R) (m : M) :
    originalLocalizedModuleAwayOverlap a b (LocalizedModule.mk m 1) =
      LocalizedModule.mk m 1 :=
  LocalizedModule.lift_mk_one (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers (a*b)) M) _ m

end LinearStudy
