module
public import Linear.KoszulHomotopyTop
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
open scoped BigOperators
namespace LinearStudy
variable {R : Type*} [CommRing R] (n : ℕ)

/-- The ACTUAL complementary-coordinate functional on the penultimate
ORIGINAL Koszul term,using the ordered original basis determinant. -/
def koszulTopComplementFunctional (i : Fin (n+1)) :
    (⋀[R]^n (Fin (n+1) → R)) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv
    ((Pi.basisFun R (Fin (n+1))).det.curryLeft ((Pi.basisFun R (Fin (n+1))) i))

/-- Original ordered complementary wedges have the actual sign (-1)^j.
Reuses mathlib AlternatingMap insertNth;no sign convention assumed. -/
theorem koszulTopComplementFunctional_basis (i j : Fin (n+1)) :
    koszulTopComplementFunctional n i
      (exteriorPower.ιMulti R n (j.removeNth (Pi.basisFun R (Fin (n+1))))) =
      if i=j then (-1:R)^(j:ℕ) else 0 := by
  classical
  let b := Pi.basisFun R (Fin (n+1))
  have hu : b.det (Function.update b j (b i))=if i=j then 1 else 0 := by
    by_cases h : i=j
    · subst i
      simp [Function.update_eq_self,Module.Basis.det_self]
    · rw [ite_eq_right h]
      exact b.det.map_eq_zero_of_eq _ (by simp [h]) h
  rw [koszulTopComplementFunctional,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply,
    ← AlternatingMap.neg_one_pow_smul_map_insertNth,Fin.insertNth_removeNth]
  change (-1:ℤ)^(j:ℕ) • b.det (Function.update b j (b i)) = _
  rw [hu]
  by_cases h : i=j <;> simp [h,← Int.cast_smul_eq_zsmul R,smul_eq_mul]

/-- Applying the ACTUAL dual top differential to this functional gives
EXACTLY the ORIGINAL equation H_i,with ordered Koszul signs cancelling. -/
theorem koszulTopComplementFunctional_differential (H : Fin (n+1) → R)
    (i : Fin (n+1)) :
    koszulTopComplementFunctional n i
      (koszulComplex.d (Fintype.linearCombination R H) n (topKoszulGenerator (n+1))) = H i := by
  classical
  have hc (j : Fin (n+1)) :
      Fintype.linearCombination R H ((Pi.basisFun R (Fin (n+1))) j)=H j := by simp
  rw [topKoszulGenerator,koszulComplex.d,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,koszulComplex.dAlternating_apply,map_sum]
  simp only [map_smul,hc,koszulTopComplementFunctional_basis,smul_eq_mul]
  simp only [mul_ite,mul_zero,Fintype.sum_ite_eq]
  calc
    (-1:R)^(i:ℕ) * H i * (-1:R)^(i:ℕ) = ((-1:R)^(i:ℕ)*(-1:R)^(i:ℕ))*H i := by ring
    _ = H i := by rw [← pow_add,Even.neg_one_pow (by exact ⟨i.val,rfl⟩),one_mul]

end LinearStudy
