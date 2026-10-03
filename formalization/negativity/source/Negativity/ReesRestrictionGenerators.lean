module
public import Negativity.ReesBaseChange
import Mathlib.Tactic
@[expose] public section
namespace Negativity
open Polynomial
open scoped TensorProduct
noncomputable section
universe u v w
variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T] [Algebra R S]

/-- Restriction on the genuine Rees image is determined by source coefficients and the
original Rees generators. No flatness or choice of generators is required. -/
theorem rees_hom_ext_on_coefficients_and_base (I : Ideal R)
    (a b : reesAlgebra (I.map (algebraMap R S)) →+* T)
    (hc : ∀ s, a (algebraMap S _ s) = b (algebraMap S _ s))
    (hp : ∀ p, a (actualReesCoefficientMap (S := S) I p) =
      b (actualReesCoefficientMap (S := S) I p)) : a = b := by
  apply RingHom.ext
  intro x
  obtain ⟨z, rfl⟩ := actual_rees_base_change_surjective (S := S) I x
  induction z using TensorProduct.inductionOn with
  | tmul s p =>
      simp only [actualReesBaseChangeMap, AlgHom.liftEquiv_tmul, Algebra.smul_def,
        map_mul, hc, hp]
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'

/-- Ring-coordinate restriction in a Rees image follows from its two actual generator kinds. -/
theorem rees_polynomial_restriction_of_generators
    {B : Type v} {B' : Type w} [CommRing B] [CommRing B'] [Algebra R T]
    (I : Ideal R) (e : B ≃+* reesAlgebra (I.map (algebraMap R S)))
    (e' : B' ≃+* reesAlgebra (I.map (algebraMap R T)))
    (r : B →+* B') (s : S →+* T)
    (hc : ∀ x, (e' (r (e.symm (algebraMap S _ x)))).1 = C (s x))
    (hp : ∀ p, (e' (r (e.symm (actualReesCoefficientMap (S := S) I p)))).1 =
      (actualReesCoefficientMap (S := S) I p).1.map s)
    (x : B) : (e' (r x)).1 = (e x).1.map s := by
  let a : reesAlgebra (I.map (algebraMap R S)) →+* T[X] :=
    (reesAlgebra (I.map (algebraMap R T))).val.toRingHom.comp
      (e'.toRingHom.comp (r.comp e.symm.toRingHom))
  let b : reesAlgebra (I.map (algebraMap R S)) →+* T[X] :=
    (mapRingHom s).comp (reesAlgebra (I.map (algebraMap R S))).val.toRingHom
  have hab : a = b := rees_hom_ext_on_coefficients_and_base I a b
    (fun y => by simpa [a, b] using hc y)
    (fun p => by simpa [a, b] using hp p)
  have h := RingHom.congr_fun hab (e x)
  simpa [a, b] using h

end
end Negativity
