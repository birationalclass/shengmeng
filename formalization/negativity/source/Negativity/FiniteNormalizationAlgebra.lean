module

public import Negativity.PerfectIntegralClosure
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.MvPolynomial
import Mathlib.Tactic

@[expose] public section
namespace Negativity
noncomputable section
open scoped nonZeroDivisors

/-- Final theorem: normalization is finite for every integral finite-type
algebra over a perfect field, without assuming that the original algebra
is normal. Noether normalization reduces to a normal polynomial ring;
the finite function-field extension includes inseparable extensions. -/
theorem finiteType_perfectField_integralClosure_finite
    (k A K L : Type*) [Field k] [PerfectField k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] : Module.Finite A (integralClosure A L) := by
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin n) k
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hfin
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg
  let : Algebra B K := ((algebraMap A K).comp g.toRingHom).toAlgebra
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr
    ((IsFractionRing.injective A K).comp hg)
  let F := FractionRing B
  let : Algebra F K := FractionRing.liftAlgebra B K
  have : IsScalarTower B F K := FractionRing.isScalarTower_liftAlgebra B K
  have : Algebra.IsIntegral B A := ⟨IsIntegral.of_finite B⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid A B⁰) K := inferInstance
  have : FiniteDimensional F K := Module.Finite.of_isLocalization B A B⁰
  let : Algebra B L := ((algebraMap A L).comp g.toRingHom).toAlgebra
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq B A K]
    change (algebraMap A L).comp g.toRingHom =
      (algebraMap K L).comp ((algebraMap A K).comp g.toRingHom)
    rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A K L])
  let : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B F L := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq B K L, IsScalarTower.algebraMap_eq B F K]
    rw [← RingHom.comp_assoc]
    rfl)
  have : FiniteDimensional F L := Module.Finite.trans K L
  have : Module.Finite B (integralClosure B L) :=
    finiteType_perfectField_normal_integralClosure_finite k B F L
  let C := integralClosure A L
  let : Algebra B C := ((algebraMap A C).comp g.toRingHom).toAlgebra
  have : IsScalarTower B A C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq B A L, IsScalarTower.algebraMap_eq B A C]
    rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A C L])
  have : IsIntegralClosure C B L := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := by
      intro x
      constructor
      · intro hx
        exact ⟨⟨x, hx.tower_top⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact isIntegral_trans (R := B) (A := A) (y : L) y.property }
  have : Module.Finite B C := Module.Finite.equiv
    (IsIntegralClosure.equiv B (integralClosure B L) L C).toLinearEquiv
  exact Module.Finite.of_restrictScalars_finite B A C

end
end Negativity
