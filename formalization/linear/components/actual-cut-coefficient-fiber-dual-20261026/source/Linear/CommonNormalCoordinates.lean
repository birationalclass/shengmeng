module
public import Linear.RectangularMinor
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Funext
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace LinearStudy

/-- The normal block of a row matrix after a generic ambient linear change. -/
def genericNormalBlock {K σ : Type*} [CommRing K] [Fintype σ]
    {c : ℕ} (A : Matrix (Fin c) σ K) (ν : Fin c → σ) :
    Matrix (Fin c) (Fin c) (MvPolynomial (σ × σ) K) :=
  (A.map MvPolynomial.C * Matrix.mvPolynomialX σ σ K).submatrix id ν

theorem eval_genericNormalBlock_det {K σ : Type*} [CommRing K] [Fintype σ]
    {c : ℕ} (A : Matrix (Fin c) σ K) (ν : Fin c → σ) (P : Matrix σ σ K) :
    MvPolynomial.eval (fun p : σ × σ => P p.1 p.2)
      (Matrix.det (genericNormalBlock A ν)) =
      Matrix.det ((A * P).submatrix id ν) := by
  classical
  rw [RingHom.map_det]
  congr 1
  ext i k
  simp [genericNormalBlock, Matrix.mul_apply]

theorem genericNormalBlock_det_ne_zero {K σ : Type*} [Field K] [Fintype σ]
    {c : ℕ} (A : Matrix (Fin c) σ K) (ν : Fin c → σ) (hν : Function.Injective ν)
    (hA : LinearIndependent K A) :
    Matrix.det (genericNormalBlock A ν) ≠ 0 := by
  classical
  obtain ⟨j, hj, hd⟩ := exists_nonzero_coordinate_minor A hA
  let P : Matrix σ σ K := Matrix.of fun u v =>
    Function.extend ν (fun k => if u = j k then 1 else 0) (fun _ => 0) v
  have hP : (A * P).submatrix id ν = fun i k => A i (j k) := by
    ext i k
    simp [Matrix.mul_apply, P, hν.extend_apply]
  intro h
  have he := eval_genericNormalBlock_det A ν P
  rw [h, map_zero, hP] at he
  exact hd he.symm

/-- One invertible ambient matrix works simultaneously for every member of a
finite family of full-row-rank matrices over an infinite field. The chosen
normal column positions are fixed in advance. -/
theorem exists_common_normal_coordinate_matrix {K σ ι : Type*}
    [Field K] [Infinite K] [Fintype σ] [DecidableEq σ] [Fintype ι]
    {c : ℕ} (ν : Fin c → σ) (hν : Function.Injective ν)
    (A : ι → Matrix (Fin c) σ K) (hA : ∀ a, LinearIndependent K (A a)) :
    ∃ P : Matrix σ σ K, Matrix.det P ≠ 0 ∧
      ∀ a, Matrix.det (((A a) * P).submatrix id ν) ≠ 0 := by
  classical
  let D := Matrix.det (Matrix.mvPolynomialX σ σ K)
  let B : ι → MvPolynomial (σ × σ) K := fun a => Matrix.det (genericNormalBlock (A a) ν)
  have hD : D ≠ 0 := Matrix.det_mvPolynomialX_ne_zero σ K
  have hB : ∀ a, B a ≠ 0 := fun a => genericNormalBlock_det_ne_zero (A a) ν hν (hA a)
  have hp : D * ∏ a, B a ≠ 0 := mul_ne_zero hD (Finset.prod_ne_zero_iff.mpr (fun a _ => hB a))
  have hx : ∃ x : σ × σ → K, MvPolynomial.eval x (D * ∏ a, B a) ≠ 0 := by
    by_contra hn
    apply hp
    apply MvPolynomial.funext
    intro x
    exact (not_ne_iff.mp (not_exists.mp hn x)).trans (map_zero _).symm
  obtain ⟨x, hx⟩ := hx
  let P : Matrix σ σ K := Matrix.of fun i j => x (i, j)
  have hprod : MvPolynomial.eval x D * ∏ a, MvPolynomial.eval x (B a) ≠ 0 := by
    simpa only [map_mul, map_prod] using hx
  refine ⟨P, ?_, ?_⟩
  · have h := (mul_ne_zero_iff.mp hprod).1
    simpa only [D, Matrix.eval_det_mvPolynomialX, P] using h
  · intro a
    have h := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).2) a (Finset.mem_univ a)
    have he := eval_genericNormalBlock_det (A a) ν P
    change MvPolynomial.eval x (B a) = _ at he
    rwa [he] at h

end LinearStudy
