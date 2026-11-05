module
public import Mathlib.RingTheory.Localization.Module
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
/-- The actual localized kernel inclusion is still killed by the actual
localized original map, without flatness or torsion assumptions. -/
theorem localizedOriginalKernelCoefficient_comp_zero
    (f : M →ₗ[R] N) (a : R) (v : LocalizedModule (Submonoid.powers a) f.ker) :
    LocalizedModule.map (Submonoid.powers a) f
      (LocalizedModule.map (Submonoid.powers a) f.ker.subtype v) = 0 := by
  induction v using LocalizedModule.induction_on with
  | h m b =>
    rw [LocalizedModule.map_mk,LocalizedModule.map_mk]
    change LocalizedModule.mk (f (m : M)) b = 0
    rw [m.property,LocalizedModule.zero_mk]
end LinearStudy
