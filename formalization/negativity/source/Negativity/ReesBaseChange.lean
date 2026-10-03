module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open Polynomial
open scoped TensorProduct
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

def actualReesCoefficientMap (I : Ideal R) :
    reesAlgebra I →ₐ[R] reesAlgebra (I.map (algebraMap R S)) where
  toFun p := ⟨p.1.map (algebraMap R S), by
    intro n
    rw [coeff_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (p.2 n)⟩
  map_one' := Subtype.ext (Polynomial.map_one _)
  map_mul' p q := Subtype.ext (Polynomial.map_mul _)
  map_zero' := Subtype.ext (Polynomial.map_zero _)
  map_add' p q := Subtype.ext (Polynomial.map_add _)
  commutes' r := by
    apply Subtype.ext
    simp

def actualReesBaseChangeMap (I : Ideal R) :
    S ⊗[R] reesAlgebra I →ₐ[S] reesAlgebra (I.map (algebraMap R S)) :=
  AlgHom.liftEquiv R S (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S)))
    (actualReesCoefficientMap I)

private theorem monomial_mem_actualReesBaseChangeRange (I : Ideal R) (n : ℕ) (s : S)
    (hs : s ∈ (I.map (algebraMap R S)) ^ n) :
    (⟨monomial n s, reesAlgebra.monomial_mem.mpr hs⟩ : reesAlgebra (I.map (algebraMap R S)))
      ∈ (actualReesBaseChangeMap (S := S) I).range := by
  rw [← Ideal.map_pow] at hs
  change s ∈ Ideal.span ((algebraMap R S) '' ((I ^ n : Ideal R) : Set R)) at hs
  have hm : ∃ p, (actualReesBaseChangeMap (S := S) I p).1 = monomial n s := by
    refine Submodule.span_induction (p := fun s _ =>
      ∃ p, (actualReesBaseChangeMap (S := S) I p).1 = monomial n s) ?_ ?_ ?_ ?_ hs
    · intro s hs
      obtain ⟨r, hr, rfl⟩ := hs
      refine ⟨1 ⊗ₜ[R] (⟨monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ : reesAlgebra I), ?_⟩
      simp [actualReesBaseChangeMap, actualReesCoefficientMap]
    · exact ⟨0, by simp⟩
    · intro x y hx hy hpx hpy
      obtain ⟨a, ha⟩ := hpx
      obtain ⟨b, hb⟩ := hpy
      refine ⟨a + b, ?_⟩
      simpa using congrArg₂ (fun a b : S[X] => a + b) ha hb
    · intro a s hs hp
      obtain ⟨b, hb⟩ := hp
      refine ⟨a • b, ?_⟩
      simpa [smul_monomial, smul_eq_mul] using congrArg (fun x : S[X] => a • x) hb
  obtain ⟨p, hp⟩ := hm
  exact ⟨p, Subtype.ext hp⟩

/-- Final theorem: the actual scalar extension of the Rees algebra
surjects onto the Rees algebra of the extended ideal. Thus the actual
graded ideal algebra on an affine chart is a cyclic module over the
base-changed Rees algebra. No flatness or characteristic assumption is
needed. The global scheme gluing is separate. -/
theorem actual_rees_base_change_surjective (I : Ideal R) :
    Function.Surjective (actualReesBaseChangeMap (S := S) I) := by
  intro p
  have hp : p ∈ (actualReesBaseChangeMap (S := S) I).range := by
    rw [reesAlgebra.as_sum_support p]
    apply Subalgebra.sum_mem
    intro n hn
    exact monomial_mem_actualReesBaseChangeRange I n (p.1.coeff n) (p.2 n)
  exact hp

end
end Negativity
