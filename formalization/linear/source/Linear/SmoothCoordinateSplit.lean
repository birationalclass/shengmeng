module
public import Linear.SmoothJacobianMinor
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.EquivFin
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- Enumerate the remaining coordinates while retaining the selected normal
coordinates in their original order. -/
theorem exists_coordinate_split {σ : Type*} [Finite σ] {c : ℕ}
    (j : Fin c → σ) (hj : Function.Injective j) :
    ∃ r : ℕ, ∃ e : (Fin r ⊕ Fin c) ≃ σ, ∀ i, e (Sum.inr i) = j i := by
  classical
  let A := Set.range j
  let := Fintype.ofFinite σ
  let eN : Fin c ≃ A := Equiv.ofInjective j hj
  let eT : Fin (Fintype.card (Aᶜ : Set σ)) ≃ (Aᶜ : Set σ) :=
    (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Aᶜ : Set σ),
    ((eT.sumCongr eN).trans (Equiv.sumComm _ _)).trans (Equiv.Set.sumCompl A), ?_⟩
  intro i
  rfl

theorem polynomial_eval_coordinate_equiv {K σ τ : Type*} [CommRing K]
    (e : τ ≃ σ) (x : σ → K) (G : MvPolynomial σ K) :
    MvPolynomial.eval (x ∘ e) (MvPolynomial.rename e.symm G) = MvPolynomial.eval x G := by
  rw [MvPolynomial.eval_rename]
  have he : (x ∘ e) ∘ e.symm = x := by
    funext i
    simp [Function.comp_def]
  rw [he]

theorem polynomial_derivative_eval_coordinate_equiv {K σ τ : Type*} [CommRing K]
    (e : τ ≃ σ) (x : σ → K) (G : MvPolynomial σ K) (a : τ) :
    MvPolynomial.eval (x ∘ e) (MvPolynomial.pderiv a (MvPolynomial.rename e.symm G)) =
      MvPolynomial.eval x (MvPolynomial.pderiv (e a) G) := by
  have h := MvPolynomial.pderiv_rename e.symm.injective (e a) G
  rw [e.symm_apply_apply] at h
  rw [h, polynomial_eval_coordinate_equiv]

theorem smooth_generators_exist_with_normal_coordinate_minor
    {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    ∃ (r c : ℕ) (e : (Fin r ⊕ Fin c) ≃ σ) (G : Fin c → MvPolynomial σ K),
      I.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))) ∧
      (∀ i, MvPolynomial.eval (x ∘ e) (MvPolynomial.rename e.symm (G i)) = 0) ∧
      IsUnit (Matrix.det (fun i j => MvPolynomial.eval (x ∘ e)
        (MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.rename e.symm (G i))))) := by
  obtain ⟨c, G, hs, hv, j, hj, hd⟩ :=
    exists_smooth_polynomial_jacobian_generators_at_point I P hIP x hP
  obtain ⟨r, e, he⟩ := exists_coordinate_split j hj
  refine ⟨r, c, e, G, hs, ?_, ?_⟩
  · intro i
    rw [polynomial_eval_coordinate_equiv]
    exact hv i
  · apply isUnit_iff_ne_zero.mpr
    have hm : (fun i k => MvPolynomial.eval (x ∘ e)
        (MvPolynomial.pderiv (Sum.inr k) (MvPolynomial.rename e.symm (G i)))) =
        (fun i k => MvPolynomial.eval x (MvPolynomial.pderiv (j k) (G i))) := by
      funext i k
      rw [polynomial_derivative_eval_coordinate_equiv, he]
    rwa [hm]

end LinearStudy
