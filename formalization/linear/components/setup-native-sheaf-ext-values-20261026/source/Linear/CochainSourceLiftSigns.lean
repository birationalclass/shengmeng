module
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- Normalize the ACTUAL source-homotopy signs in the SAME source degrees. -/
def cochainSourceLiftSigns {K L : CochainComplex A ℤ} (q : ℤ)
    (t : Cochain K L (q-1)) : Cochain K L (q-1) :=
  Cochain.mk (fun j k h => ((q+1)*j).negOnePow • t.v j k h)

/-- The normalized top lift starts with the SAME actual functional. -/
theorem cochainSourceLiftSigns_top {K L : CochainComplex A ℤ} (q : ℤ)
    (t : Cochain K L (q-1)) (a : K.X (-q) ⟶ L.X 0)
    (h : q.negOnePow • K.d (-q) (-q+1) ≫ t.v (-q+1) 0 (by omega) = -a) :
    K.d (-q) (-q+1) ≫ (cochainSourceLiftSigns q t).v (-q+1) 0 (by omega) = a := by
  have hs : ((q+1)*(-q+1)).negOnePow = -q.negOnePow := by
    rw [show (q+1)*(-q+1)=1-q*q by ring,Int.negOnePow_sub,
      Int.negOnePow_mul_self,Int.negOnePow_one,neg_mul,one_mul]
  simp only [cochainSourceLiftSigns,Cochain.mk_v,hs,Units.neg_smul]
  simpa only [Units.smul_def,Preadditive.comp_neg,Preadditive.comp_zsmul] using
    (neg_eq_iff_eq_neg.mpr h)

/-- Every normalized intermediate component is an ACTUAL positive-sign
lifting recursion;the correction is proved from the native sign. -/
theorem cochainSourceLiftSigns_middle {K L : CochainComplex A ℤ} (q j : ℤ)
    (t : Cochain K L (q-1))
    (h : t.v j (j+q-1) (by omega) ≫ L.d (j+q-1) (j+q) +
      q.negOnePow • K.d j (j+1) ≫ t.v (j+1) (j+q) (by omega) = 0) :
    (cochainSourceLiftSigns q t).v j (j+q-1) (by omega) ≫ L.d (j+q-1) (j+q) =
      K.d j (j+1) ≫ (cochainSourceLiftSigns q t).v (j+1) (j+q) (by omega) := by
  have hs : ((q+1)*(j+1)).negOnePow =
      -(((q+1)*j).negOnePow * q.negOnePow) := by
    rw [mul_add,mul_one,Int.negOnePow_add,Int.negOnePow_succ,mul_neg]
  have he := congrArg (fun f => ((q+1)*j).negOnePow • f) (add_eq_zero_iff_eq_neg.mp h)
  rw [smul_neg,smul_smul,← Units.neg_smul] at he
  simpa only [cochainSourceLiftSigns,Cochain.mk_v,hs,Units.smul_def,
    Preadditive.comp_zsmul,Preadditive.zsmul_comp] using he

/-- The normalized bottom component preserves the SAME actual augmentation
and cocycle,with NO residual degree sign. -/
theorem cochainSourceLiftSigns_bottom {K L : CochainComplex A ℤ} (q : ℤ)
    (t : Cochain K L (q-1)) {E : A}
    (alpha : K.X 0 ⟶ E) (c : E ⟶ L.X q)
    (h : t.v 0 (q-1) (zero_add _) ≫ L.d (q-1) q = alpha ≫ c) :
    (cochainSourceLiftSigns q t).v 0 (q-1) (zero_add _) ≫ L.d (q-1) q = alpha ≫ c := by
  simpa only [cochainSourceLiftSigns,Cochain.mk_v,mul_zero,Int.negOnePow_zero,one_smul] using h

end LinearStudy
