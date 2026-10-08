module
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open scoped RatFunc
attribute [local instance] Polynomial.algebra

def transcendentalAdjoinScalarInclusion
    (K E F : Type*) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra E F] [Algebra K F] [IsScalarTower K E F]
    (t : F) :
      IntermediateField.adjoin K {t} →ₐ[K] IntermediateField.adjoin E {t} := by
  have hle : IntermediateField.adjoin K {t} ≤
      (IntermediateField.adjoin E {t}).restrictScalars K := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    exact IntermediateField.subset_adjoin E _ hz
  exact { (IntermediateField.inclusion hle).toRingHom with
    commutes' := by
      intro a
      apply Subtype.ext
      exact ((IntermediateField.adjoin E {t}).val.restrictScalars K).commutes a |>.symm }

/-- Adjoining the SAME actual transcendental element preserves the
finite coefficient extension degree. The natural inclusion is constructed. -/
theorem transcendental_adjoin_base_finrank
    (K E F : Type*) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra E F] [Algebra K F] [IsScalarTower K E F]
    [Algebra.IsAlgebraic K E] (t : F) (ht : Transcendental E t) :
    letI : Algebra (IntermediateField.adjoin K {t}) (IntermediateField.adjoin E {t}) :=
      (transcendentalAdjoinScalarInclusion K E F t).toRingHom.toAlgebra
    Module.finrank (IntermediateField.adjoin K {t}) (IntermediateField.adjoin E {t}) =
      Module.finrank K E := by
  let L := IntermediateField.adjoin K {t}
  let M := IntermediateField.adjoin E {t}
  letI : Algebra L M := (transcendentalAdjoinScalarInclusion K E F t).toRingHom.toAlgebra
  let eK := RatFunc.algEquivOfTranscendental t (ht.of_tower_top K)
  let eE := RatFunc.algEquivOfTranscendental t ht
  have hc : (algebraMap L M).comp eK.toRingEquiv.toRingHom =
      eE.toRingEquiv.toRingHom.comp (algebraMap (RatFunc K) (RatFunc E)) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial K)
    intro P
    apply Subtype.ext
    simp only [RingHom.comp_apply]
    simp only [RingHom.algebraMap_toAlgebra, transcendentalAdjoinScalarInclusion,
      IntermediateField.coe_inclusion]
    change (eK (algebraMap (Polynomial K) (RatFunc K) P) : F) =
      (eE (algebraMap (RatFunc K) (RatFunc E)
        (algebraMap (Polynomial K) (RatFunc K) P)) : F)
    have hm : algebraMap (RatFunc K) (RatFunc E)
        (algebraMap (Polynomial K) (RatFunc K) P) =
        algebraMap (Polynomial E) (RatFunc E)
          (algebraMap (Polynomial K) (Polynomial E) P) :=
      (IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (RatFunc E) P).symm.trans
        (IsScalarTower.algebraMap_apply (Polynomial K) (Polynomial E) (RatFunc E) P)
    rw [hm]
    simp [eK, eE, RatFunc.algEquivOfTranscendental_algebraMap,
      Polynomial.algebraMap_eq, Polynomial.aeval_map_algebraMap]
    exact IntermediateField.aeval_coe (S := M) (R := K) (IntermediateField.AdjoinSimple.gen E t) P
  have h := Algebra.finrank_eq_of_equiv_equiv eK.toRingEquiv eE.toRingEquiv hc
  rw [← h]
  exact RatFunc.finrank_ratFunc_ratFunc K E

end LinearStudy
