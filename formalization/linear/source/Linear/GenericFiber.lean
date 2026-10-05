module

public import Linear.Reduction
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.Module

/-!
# Descending annihilation from the generic fiber

Flatness makes localization at the base's nonzerodivisors injective. Thus the
SS annihilation identity, once proved in the localized algebra, descends to A.
The localized SS identity itself remains an explicit input here.
-/

@[expose] public section

namespace LinearStudy

variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C]
  [Algebra B A] [Algebra B C] [Module.Flat B A]

/-- Localization at base nonzerodivisors is injective on a flat algebra. -/
theorem flat_genericFiber_injective (f : A →ₐ[B] C)
    [IsLocalizedModule (nonZeroDivisors B) f.toLinearMap] :
    Function.Injective f := by
  apply (IsLocalizedModule.injective_iff_isRegular
    (nonZeroDivisors B) f.toLinearMap).mpr
  intro c
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors c.property

/-- Descend the localized ideal-annihilation identity without assuming the
localization map is injective: derive that fact from flatness. -/
theorem flat_genericFiber_descend_annihilation (f : A →ₐ[B] C)
    [IsLocalizedModule (nonZeroDivisors B) f.toLinearMap]
    (N : Ideal A) (delta : A)
    (hgeneric : Annihilates (N.map f.toRingHom) (f delta)) :
    Annihilates N delta := by
  intro n hn
  apply flat_genericFiber_injective f
  rw [map_mul, map_zero]
  exact hgeneric (f n) (Ideal.mem_map_of_mem f.toRingHom hn)

end LinearStudy
