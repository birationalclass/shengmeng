module
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.DirectSum.Algebra
public import Negativity.ReesBaseChange
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section
namespace Negativity
open Polynomial
open scoped DirectSum
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {R : Type u} [CommRing R] (I : Ideal R)

def actualReesPowerMonomial (n : ℕ) : ↥(I ^ n) →ₗ[R] reesAlgebra I where
  toFun r := ⟨monomial n r.1, reesAlgebra.monomial_mem.mpr r.2⟩
  map_add' a b := Subtype.ext ((monomial n).map_add a.1 b.1)
  map_smul' r a := Subtype.ext ((monomial n).map_smul r a.1)

/-- The existing Mathlib external graded ring maps to the actual polynomial
Rees algebra by sending its degree-n coefficient to a monomial of degree n. -/
def actualDirectSumToRees : (⨁ n : ℕ, ↥(I ^ n)) →ₐ[R] reesAlgebra I :=
  DirectSum.toAlgebra R _ (actualReesPowerMonomial I)
    (by apply Subtype.ext; change monomial 0 (1 : R) = 1; simp)
    (by
      intro n m a b
      apply Subtype.ext
      change monomial (n + m) (a.1 * b.1) = monomial n a.1 * monomial m b.1
      rw [monomial_mul_monomial])

@[simp]
theorem actualDirectSumToRees_lof (n : ℕ) (r : ↥(I ^ n)) :
    actualDirectSumToRees I (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n r) =
      actualReesPowerMonomial I n r := by
  simp [actualDirectSumToRees, DirectSum.toAlgebra, DirectSum.lof_eq_of]

/-- Extraction of the actual polynomial coefficient is the same as the
corresponding graded coefficient. -/
theorem actualDirectSumToRees_coeff (a : ⨁ n : ℕ, ↥(I ^ n)) (n : ℕ) :
    (actualDirectSumToRees I a).1.coeff n = (a n).1 := by
  classical
  have h : (Polynomial.lcoeff R n).comp
      ((reesAlgebra I).val.toLinearMap.comp (actualDirectSumToRees I).toLinearMap) =
      (I ^ n).subtype.comp (DirectSum.component R ℕ (fun n => ↥(I ^ n)) n) := by
    apply DirectSum.linearMap_ext
    intro m
    ext r
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      actualDirectSumToRees_lof]
    change (monomial m r.1).coeff n =
      ((DirectSum.component R ℕ (fun n => ↥(I ^ n)) n)
        (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) m r)).1
    rw [DirectSum.component.of]
    by_cases hm : m = n
    · subst m; simp
    · simp [coeff_monomial, hm]
  exact LinearMap.congr_fun h a

theorem actualDirectSumToRees_bijective :
    Function.Bijective (actualDirectSumToRees I) := by
  classical
  constructor
  · intro a b hab
    ext n
    calc
      (a n).1 = (actualDirectSumToRees I a).1.coeff n :=
        (actualDirectSumToRees_coeff I a n).symm
      _ = (actualDirectSumToRees I b).1.coeff n := congrArg (fun p => p.1.coeff n) hab
      _ = (b n).1 := actualDirectSumToRees_coeff I b n
  · intro p
    let a : ⨁ n : ℕ, ↥(I ^ n) := ∑ n ∈ p.1.support,
      DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n ⟨p.1.coeff n, p.2 n⟩
    refine ⟨a, ?_⟩
    simp only [a, map_sum, actualDirectSumToRees_lof]
    exact (reesAlgebra.as_sum_support p).symm

/-- Actual polynomial Rees coordinates and the Mathlib direct-sum graded
ring are isomorphic as algebras over R, including in arbitrary characteristic. -/
def actualReesDirectSumAlgEquiv : (⨁ n : ℕ, ↥(I ^ n)) ≃ₐ[R] reesAlgebra I :=
  AlgEquiv.ofBijective (actualDirectSumToRees I) (actualDirectSumToRees_bijective I)

@[simp]
theorem actualReesDirectSumAlgEquiv_lof (n : ℕ) (r : ↥(I ^ n)) :
    actualReesDirectSumAlgEquiv I (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n r) =
      actualReesPowerMonomial I n r :=
  actualDirectSumToRees_lof I n r

@[simp]
theorem actualReesDirectSumAlgEquiv_symm_monomial (n : ℕ) (r : ↥(I ^ n)) :
    (actualReesDirectSumAlgEquiv I).symm (actualReesPowerMonomial I n r) =
      DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n r := by
  apply (actualReesDirectSumAlgEquiv I).injective
  rw [AlgEquiv.apply_symm_apply, actualReesDirectSumAlgEquiv_lof]

/-- An already constructed genuine direct-sum Rees action is transported
through the proved algebra isomorphism to the polynomial Rees algebra. -/
@[instance_reducible]
def actualPolynomialReesModule (M : Type w) [AddCommMonoid M]
    [Module (⨁ n : ℕ, ↥(I ^ n)) M] : Module (reesAlgebra I) M :=
  Module.compHom M (actualReesDirectSumAlgEquiv I).symm.toRingHom

@[simp]
theorem actualPolynomialReesModule_monomial_smul (M : Type w) [AddCommMonoid M]
    [Module (⨁ n : ℕ, ↥(I ^ n)) M] (n : ℕ) (r : ↥(I ^ n)) (x : M) :
    letI := actualPolynomialReesModule I M
    actualReesPowerMonomial I n r • x =
      (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n r) • x := by
  letI := actualPolynomialReesModule I M
  change (actualReesDirectSumAlgEquiv I).symm (actualReesPowerMonomial I n r) • x = _
  rw [actualReesDirectSumAlgEquiv_symm_monomial]

/-- Finite generation is preserved when the genuinely equivalent Rees scalar
ring is expressed in polynomial coordinates. -/
theorem actualPolynomialReesModule_finite_iff (M : Type w) [AddCommMonoid M]
    [Module (⨁ n : ℕ, ↥(I ^ n)) M] :
    letI := actualPolynomialReesModule I M
    Module.Finite (reesAlgebra I) M ↔ Module.Finite (⨁ n : ℕ, ↥(I ^ n)) M := by
  letI := actualPolynomialReesModule I M
  let e : M →ₛₗ[(actualReesDirectSumAlgEquiv I).symm.toRingHom] M :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : RingHomSurjective (actualReesDirectSumAlgEquiv I).symm.toRingHom :=
    ⟨(actualReesDirectSumAlgEquiv I).symm.surjective⟩
  exact LinearMap.finite_iff_of_bijective e Function.bijective_id

#print axioms actualReesDirectSumAlgEquiv
#print axioms actualPolynomialReesModule_monomial_smul
#print axioms actualPolynomialReesModule_finite_iff
end
end Negativity
