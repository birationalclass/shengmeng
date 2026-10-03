module
public import Negativity.ReesDirectSumBaseChange
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section
namespace Negativity
open Polynomial
universe u v
noncomputable section
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Changing affine global-section coordinates changes the Rees ring by
the actual coefficientwise polynomial ring isomorphism. -/
def actualReesRingEquiv (I : Ideal R) (e : R ≃+* S) :
    reesAlgebra I ≃+* reesAlgebra (I.map e.toRingHom) where
  toFun p := ⟨p.1.map e.toRingHom, by
    intro n
    rw [coeff_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem e.toRingHom (p.2 n)⟩
  invFun p := ⟨p.1.map e.symm.toRingHom, by
    intro n
    rw [coeff_map]
    have hp := p.2 n
    rw [← Ideal.map_pow] at hp
    exact (Ideal.symm_apply_mem_of_equiv_iff (f := e)).mpr hp⟩
  left_inv p := by
    apply Subtype.ext
    change (Polynomial.mapEquiv e).symm ((Polynomial.mapEquiv e) p.1) = p.1
    exact (Polynomial.mapEquiv e).symm_apply_apply p.1
  right_inv p := by
    apply Subtype.ext
    change (Polynomial.mapEquiv e) ((Polynomial.mapEquiv e).symm p.1) = p.1
    exact (Polynomial.mapEquiv e).apply_symm_apply p.1
  map_mul' p q := Subtype.ext (Polynomial.map_mul _)
  map_add' p q := Subtype.ext (Polynomial.map_add _)

@[simp]
theorem actualReesRingEquiv_coeff (I : Ideal R) (e : R ≃+* S)
    (p : reesAlgebra I) (n : ℕ) :
    (actualReesRingEquiv I e p).1.coeff n = e (p.1.coeff n) := by
  exact coeff_map e.toRingHom n

@[simp]
theorem actualReesRingEquiv_monomial (I : Ideal R) (e : R ≃+* S)
    (n : ℕ) (r : ↥(I ^ n)) :
    actualReesRingEquiv I e (actualReesPowerMonomial I n r) =
      actualReesPowerMonomial (I.map e.toRingHom) n
        ⟨e r.1, by
          rw [← Ideal.map_pow]
          exact Ideal.mem_map_of_mem e.toRingHom r.2⟩ := by
  apply Subtype.ext
  exact Polynomial.map_monomial _

#print axioms actualReesRingEquiv
#print axioms actualReesRingEquiv_monomial
end
end Negativity
