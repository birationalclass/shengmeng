module

public import Linear.PolynomialDiagonal
public import Linear.DeterminantAnnihilator
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
open scoped TensorProduct
namespace LinearStudy
variable {K A ι : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype ι] [DecidableEq ι]

theorem polynomial_tensor_diagonal_eq_coordinate_ideal
    (q : MvPolynomial ι K →ₐ[K] A) (hq : Function.Surjective q) :
    Ideal.span (Set.range (fun i =>
      q (MvPolynomial.X i) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] q (MvPolynomial.X i))) =
      KaehlerDifferential.ideal K A := by
  classical
  let l : A →ₐ[K] A ⊗[K] A := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[K] A ⊗[K] A := Algebra.TensorProduct.includeRight
  let u := l.toRingHom.comp q.toRingHom
  let v := r.toRingHom.comp q.toRingHom
  let pi := (Algebra.TensorProduct.lmul' K : A ⊗[K] A →ₐ[K] A).toRingHom
  let D : Ideal (A ⊗[K] A) := Ideal.span (Set.range (fun i =>
    q (MvPolynomial.X i) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] q (MvPolynomial.X i)))
  have hC : ∀ c, u (MvPolynomial.C c) = v (MvPolynomial.C c) := by
    intro c
    change l (q (MvPolynomial.C c)) = r (q (MvPolynomial.C c))
    change l (q (algebraMap K (MvPolynomial ι K) c)) =
      r (q (algebraMap K (MvPolynomial ι K) c))
    rw [q.commutes, l.commutes, r.commutes]
  have hX : ∀ i, pi (u (MvPolynomial.X i)) = pi (v (MvPolynomial.X i)) := by
    intro i
    simp [pi, u, v, l, r]
  have hall : ∀ a : A, l a - r a ∈ D := by
    intro a
    obtain ⟨p, rfl⟩ := hq a
    obtain ⟨b, hb, _⟩ := polynomial_diagonal_difference u v pi hC hX p
    change u p - v p ∈ D
    rw [hb]
    apply Submodule.sum_mem
    intro i hi
    exact Ideal.mul_mem_left D _ (Ideal.subset_span (Set.mem_range_self i))
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp [KaehlerDifferential.ideal, RingHom.mem_ker]
  · rw [← KaehlerDifferential.span_range_eq_ideal]
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change (1 : A) ⊗ₜ[K] a - a ⊗ₜ[K] (1 : A) ∈ D
    simpa only [l, r, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, neg_sub] using D.neg_mem (hall a)

theorem polynomialQuotient_diagonal_jacobian (P : ι → MvPolynomial ι K) :
    let Q := MvPolynomial ι K ⧸ Ideal.span (Set.range P)
    let q := Ideal.Quotient.mk (Ideal.span (Set.range P))
    ∃ D : Matrix ι ι (Q ⊗[K] Q),
      Annihilates (KaehlerDifferential.ideal K Q) D.det ∧
      Algebra.TensorProduct.lmul' K D.det =
        Matrix.det (fun i j => q (MvPolynomial.pderiv j (P i))) := by
  classical
  let Q := MvPolynomial ι K ⧸ Ideal.span (Set.range P)
  let q := Ideal.Quotient.mkₐ K (Ideal.span (Set.range P))
  let l : Q →ₐ[K] Q ⊗[K] Q := Algebra.TensorProduct.includeLeft
  let r : Q →ₐ[K] Q ⊗[K] Q := Algebra.TensorProduct.includeRight
  let u := l.toRingHom.comp q.toRingHom
  let v := r.toRingHom.comp q.toRingHom
  let pi := (Algebra.TensorProduct.lmul' K : Q ⊗[K] Q →ₐ[K] Q).toRingHom
  have hC : ∀ c, u (MvPolynomial.C c) = v (MvPolynomial.C c) := by
    intro c
    change l (q (MvPolynomial.C c)) = r (q (MvPolynomial.C c))
    change l (q (algebraMap K (MvPolynomial ι K) c)) =
      r (q (algebraMap K (MvPolynomial ι K) c))
    rw [q.commutes, l.commutes, r.commutes]
  have hX : ∀ i, pi (u (MvPolynomial.X i)) = pi (v (MvPolynomial.X i)) := by
    intro i
    simp [pi, u, v, l, r]
  choose D hD hd using fun (i : ι) => polynomial_diagonal_difference
    (R := K) (A := Q ⊗[K] Q) (B := Q) (ι := ι) u v pi hC hX (P i)
  let M : Matrix ι ι (Q ⊗[K] Q) := D
  have he : M.mulVec (fun i => q (MvPolynomial.X i) ⊗ₜ[K] (1 : Q) -
      (1 : Q) ⊗ₜ[K] q (MvPolynomial.X i)) = 0 := by
    funext i
    have hp : q (P i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))
    have h := hD i
    change q (P i) ⊗ₜ[K] (1 : Q) - (1 : Q) ⊗ₜ[K] q (P i) =
      ∑ j, D i j * (q (MvPolynomial.X j) ⊗ₜ[K] (1 : Q) -
        (1 : Q) ⊗ₜ[K] q (MvPolynomial.X j)) at h
    rw [hp] at h
    simpa [M, Matrix.mulVec, dotProduct] using h.symm
  refine ⟨M, ?_, ?_⟩
  · rw [← polynomial_tensor_diagonal_eq_coordinate_ideal q Ideal.Quotient.mk_surjective]
    exact determinant_annihilates_coordinate_ideal M _ he
  · change pi M.det = Matrix.det (fun i j => q (MvPolynomial.pderiv j (P i)))
    calc
      pi M.det = Matrix.det (fun i j => pi (M i j)) := RingHom.map_det pi M
      _ = Matrix.det (fun i j => q (MvPolynomial.pderiv j (P i))) := by
        congr 1
        funext i j
        simpa [pi, u, l, M] using hd i j

end LinearStudy
