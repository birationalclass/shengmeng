module

public import Negativity.FiniteFrobenius
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: finite integral closure survives a finite purely
inseparable field extension over a finitely generated perfect-field
algebra. Frobenius finiteness is derived; the actual top integral closure
embeds linearly into the lower closure with Frobenius-twisted scalars.
This is the purely inseparable auxiliary step of normalization finiteness;
the finite lower closure is supplied by the separate separable trace step. -/
theorem finiteType_perfectField_integralClosure_purelyInseparable_finite
    (k A E L : Type*) [Field k] [CommRing A] [Field E] [Field L]
    [Algebra k A] [Algebra.FiniteType k A]
    [Algebra A E] [Algebra A L] [Algebra E L] [IsScalarTower A E L]
    [IsPurelyInseparable E L] [FiniteDimensional E L]
    [Module.Finite A (integralClosure A E)]
    (p : ℕ) [ExpChar k p] [ExpChar A p] [ExpChar E p] [PerfectRing k p] :
    Module.Finite A (integralClosure A L) := by
  let : IsPurelyInseparable.HasExponent E L := inferInstance
  let n := IsPurelyInseparable.exponent E L
  let F : L →+* E := IsPurelyInseparable.iterateFrobenius E L p (n := n) le_rfl
  let T := integralClosure A L
  let S := integralClosure A E
  have hint (x : T) : IsIntegral A (F (x : L)) := by
    apply (isIntegral_algebraMap_iff (R := A) (A := E) (B := L)).mp
    rw [IsPurelyInseparable.algebraMap_iterateFrobenius E p (n := n) le_rfl]
    exact x.property.pow _
  let φ : T →+* S := {
    toFun x := ⟨F (x : L), hint x⟩
    map_zero' := Subtype.ext (map_zero F)
    map_one' := Subtype.ext (map_one F)
    map_add' x y := Subtype.ext (map_add F (x : L) (y : L))
    map_mul' x y := Subtype.ext (map_mul F (x : L) (y : L)) }
  let b : A →+* S := algebraMap A S
  have hscalar (a : A) : φ (algebraMap A T a) = b (_root_.iterateFrobenius A p n a) := by
    apply Subtype.ext
    change F (algebraMap A L a) = algebraMap A E (_root_.iterateFrobenius A p n a)
    rw [IsScalarTower.algebraMap_apply A E L,
      IsPurelyInseparable.iterateFrobenius_algebraMap L p (K := E) (n := n) le_rfl]
    simp only [_root_.iterateFrobenius_def, map_pow]
  have hb : b.Finite := RingHom.finite_algebraMap.mpr inferInstance
  have htw : (b.comp (_root_.iterateFrobenius A p n)).Finite :=
    hb.comp (finiteType_perfectField_iterateFrobenius_finite k A p n)
  let : Algebra A S := (b.comp (_root_.iterateFrobenius A p n)).toAlgebra
  have : Module.Finite A S := htw
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let l : T →ₗ[A] S := {
    __ := φ.toAddMonoidHom
    map_smul' a x := by
      simp only [Algebra.smul_def, RingHom.id_apply]
      change φ (algebraMap A T a * x) = b (_root_.iterateFrobenius A p n a) * φ x
      rw [map_mul, hscalar] }
  apply Module.Finite.of_injective l
  intro x y h
  apply Subtype.ext
  exact F.injective (congrArg Subtype.val h)

end
end Negativity
