import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.Tactic

/-!
Derive a commuting multiplicative decomposition from mathlib's additive
Jordan-Chevalley theorem. No Jordan basis or geometric objects are assumed.
Main theorem: `multiplicativeDecomposition`.
-/

noncomputable section
namespace JordanSize
variable {K V : Type*} [Field K] [PerfectField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An invertible endomorphism has commuting semisimple and unipotent factors.
The semisimple factor is a polynomial in the original operator. -/
theorem multiplicativeDecomposition (T : Module.End K V) (hT : IsUnit T) :
    ∃ S U : Module.End K V,
      S ∈ Algebra.adjoin K {T} ∧ S.IsSemisimple ∧ IsUnit S ∧
      IsNilpotent (U-1) ∧ IsUnit U ∧ Commute S U ∧ T = S*U := by
  obtain ⟨D, hDmem, S, hSmem, hD, hS, hsum⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := T)
  have hcDT : Commute D T := (Algebra.commute_of_mem_adjoin_self hDmem).symm
  have hcDS : Commute D S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hSmem hcDT
  have hcancel : T + -D = S := by rw [hsum]; abel
  have hSunit : IsUnit S := by
    simpa only [hcancel] using hD.neg.isUnit_add_left_of_commute hT hcDT.neg_left
  let U := 1 + (↑hSunit.unit⁻¹ : Module.End K V)*D
  have hcDI : Commute D (↑hSunit.unit⁻¹ : Module.End K V) := by
    apply Commute.units_inv_right
    simpa only [hSunit.unit_spec] using hcDS
  have hID : IsNilpotent ((↑hSunit.unit⁻¹ : Module.End K V)*D) :=
    hcDI.symm.isNilpotent_mul_left hD
  have hcSI : Commute S (↑hSunit.unit⁻¹ : Module.End K V) := by
    apply Commute.units_inv_right
    simpa only [hSunit.unit_spec] using (Commute.refl S)
  have hSU : Commute S U :=
    (Commute.one_right S).add_right (hcSI.mul_right hcDS.symm)
  have hSI : S*(↑hSunit.unit⁻¹ : Module.End K V)=1 := by
    simpa only [hSunit.unit_spec] using
      (show (↑hSunit.unit : Module.End K V)*↑hSunit.unit⁻¹=1 by simp)
  have hfactor : S*U=D+S := by
    dsimp [U]
    rw [mul_add,mul_one,← mul_assoc,hSI,one_mul,add_comm]
  refine ⟨S,U,hSmem,hS,hSunit,?_,hID.isUnit_one_add,hSU,?_⟩
  · simpa only [U,add_sub_cancel_left] using hID
  · exact hsum.trans hfactor.symm

end JordanSize
#print axioms JordanSize.multiplicativeDecomposition
