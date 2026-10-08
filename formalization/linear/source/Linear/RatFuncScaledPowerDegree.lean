module
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.LinearAlgebra.Dimension.Finrank
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Scaling the degree-q variable by a nonzero coefficient does not
change the actual rational-function extension degree. -/
theorem ratFunc_scaled_power_finrank
    {E : Type*} [Field E] (u : E) (hu : u ≠ 0) (q : ℕ) :
    Module.finrank
      (IntermediateField.adjoin E
        {algebraMap (Polynomial E) (RatFunc E) (Polynomial.C u * Polynomial.X ^ q)})
      (RatFunc E) = q := by
  rw [RatFunc.finrank_eq_max_natDegree, RatFunc.num_algebraMap,
    RatFunc.denom_algebraMap, Polynomial.natDegree_one,
    Polynomial.natDegree_C_mul hu, Polynomial.natDegree_X_pow, max_eq_left (Nat.zero_le _)]

/-- Transfer the degree formula to a field with an ACTUAL rational-function
isomorphism, rather than assuming the extension degree. -/
theorem rationalField_scaled_power_finrank
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    (e : RatFunc E ≃ₐ[E] F) (u : E) (hu : u ≠ 0) (q : ℕ) :
    Module.finrank
      (IntermediateField.adjoin E {algebraMap E F u * e RatFunc.X ^ q}) F = q := by
  let a := algebraMap (Polynomial E) (RatFunc E) (Polynomial.C u * Polynomial.X ^ q)
  let K := IntermediateField.adjoin E {a}
  have he : e a = algebraMap E F u * e RatFunc.X ^ q := by
    simp only [a, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rw [← RatFunc.algebraMap_eq_C, e.commutes]
  have hK : K.map e.toAlgHom =
      IntermediateField.adjoin E {algebraMap E F u * e RatFunc.X ^ q} := by
    rw [IntermediateField.adjoin_map]
    change IntermediateField.adjoin E (e '' {a}) = _
    rw [Set.image_singleton, he]
  let i := (K.equivMap e.toAlgHom).trans (IntermediateField.equivOfEq hK)
  have h := Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv e.toRingEquiv (by ext z; rfl)
  rw [← h]
  exact ratFunc_scaled_power_finrank u hu q

end LinearStudy
