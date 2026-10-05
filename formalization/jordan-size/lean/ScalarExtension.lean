import PowerFactors
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Polynomial.Tower
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace JordanSize
open scoped TensorProduct
variable {K V L : Type*} [Field K] [PerfectField K] [Field L] [Algebra K L]
 [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 {T : Module.End K V}

lemma semisimple_baseChange (S : Module.End K V) (hS : S.IsSemisimple) :
    Module.End.IsSemisimple (S.baseChange L : Module.End L (L ⊗[K] V)) := by
  have hp := (PerfectField.separable_iff_squarefree.mpr hS.minpoly_squarefree).map (f := algebraMap K L)
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.squarefree
  rw [Polynomial.aeval_map_algebraMap]
  change Polynomial.aeval ((Module.End.baseChangeHom K L V) S) (minpoly K S) = 0
  rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

def Factors.baseChange (F : Factors T) : Factors ((Module.End.baseChangeHom K L V) T) where
  s := (Module.End.baseChangeHom K L V) F.s
  u := (Module.End.baseChangeHom K L V) F.u
  semisimple := semisimple_baseChange F.s F.semisimple
  s_unit := F.s_unit.map (Module.End.baseChangeHom K L V)
  u_unit := F.u_unit.map (Module.End.baseChangeHom K L V)
  unipotent := by
    have h := F.unipotent.map (Module.End.baseChangeHom K L V)
    simpa only [map_sub, map_one] using h
  commute := F.commute.map (Module.End.baseChangeHom K L V)
  factor := by
    have h := congrArg (Module.End.baseChangeHom K L V) F.factor
    simpa only [map_mul] using h

variable [Algebra ℚ K] [Algebra ℚ L] [IsScalarTower ℚ K L]
 [Module ℚ V] [IsScalarTower ℚ K V]
lemma log_baseChange (F : Factors T) :
    (F.baseChange (L := L)).log = (Module.End.baseChangeHom K L V) F.log := by
  apply nilpotent_exp_injective (F.baseChange (L := L)).log_nilpotent
    (F.log_nilpotent.map (Module.End.baseChangeHom K L V))
  have he := F.log_nilpotent.map_exp (Module.End.baseChangeHom K L V)
  rw [(F.baseChange (L := L)).exp_log, ← he, F.exp_log]
  rfl
end JordanSize
#print axioms JordanSize.Factors.baseChange
#print axioms JordanSize.log_baseChange
