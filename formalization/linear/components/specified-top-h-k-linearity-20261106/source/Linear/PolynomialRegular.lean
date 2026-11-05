module

public import Linear.PowerSeriesRegular
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
open Polynomial RingTheory.Sequence
open scoped Pointwise
namespace LinearStudy
variable {R : Type*} [CommRing R]

theorem polynomial_cons_X_regular (rs : List R) (hr : IsRegular R rs) :
    IsRegular R[X] (Polynomial.X :: rs.map Polynomial.C) := by
  rw [isRegular_cons_iff]
  refine ⟨?_, ?_⟩
  · exact (Polynomial.isRegular_X (R := R)).left
  · have hs : (Polynomial.X : R[X]) • (⊤ : Submodule R[X] R[X]) =
        (Ideal.span {Polynomial.X} : Ideal R[X]) := by
      rw [← Submodule.ideal_span_singleton_smul]
      exact Ideal.mul_top _
    have hk : (Ideal.span {Polynomial.X} : Ideal R[X]) =
        RingHom.ker (Polynomial.constantCoeff (R := R)) := by
      ext f
      simp [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    let e := ((Submodule.quotEquivOfEq _ _ hs).toAddEquiv.trans
      (Ideal.quotEquivOfEq hk).toAddEquiv).trans
      (RingHom.quotientKerEquivOfSurjective
        (f := Polynomial.constantCoeff (R := R))
        (fun r => ⟨Polynomial.C r, by simp⟩)).toAddEquiv
    apply (e.isRegular_congr (as := rs.map Polynomial.C) (bs := rs) ?_).mpr hr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_same.mpr
    intro r hr x
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
    change Polynomial.constantCoeff (Polynomial.C r * f) = r * Polynomial.constantCoeff f
    simp

theorem polynomial_variables_regular [Nontrivial R] (n : ℕ) :
    IsRegular (MvPolynomial (Fin n) R)
      (List.ofFn (MvPolynomial.X (σ := Fin n) (R := R))) := by
  induction n with
  | zero => simpa using IsRegular.nil (MvPolynomial (Fin 0) R) _
  | succ n ih =>
    apply (regular_transport_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv _).mpr
    simpa [List.ofFn_succ, List.map_ofFn, Function.comp_def,
      MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.finSuccEquiv_X_zero] using
        polynomial_cons_X_regular _ ih

def polynomialTranslation {ι : Type*} (a : ι → R) :
    MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R where
  toFun := MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i))
  invFun := MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (a i))
  left_inv := by
    intro p
    have h : (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (a i))).comp
        (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i))) =
        AlgHom.id R (MvPolynomial ι R) := by
      ext i
      simp
    exact DFunLike.congr_fun h p
  right_inv := by
    intro p
    have h : (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i))).comp
        (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (a i))) =
        AlgHom.id R (MvPolynomial ι R) := by
      ext i
      simp
    exact DFunLike.congr_fun h p
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' := by intro c; simp

@[simp] theorem polynomialTranslation_X {ι : Type*} (a : ι → R) (i : ι) :
    polynomialTranslation a (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (a i) := by
  simp [polynomialTranslation]

theorem polynomial_centered_variables_regular [Nontrivial R] (n : ℕ) (a : Fin n → R) :
    IsRegular (MvPolynomial (Fin n) R)
      (List.ofFn (fun i => MvPolynomial.X i - MvPolynomial.C (a i))) := by
  have h := (regular_transport_ringEquiv (polynomialTranslation (fun i => -a i)).toRingEquiv
    (List.ofFn (MvPolynomial.X (σ := Fin n) (R := R)))).mp (polynomial_variables_regular n)
  simpa [List.map_ofFn, Function.comp_def, sub_eq_add_neg] using h

end LinearStudy
