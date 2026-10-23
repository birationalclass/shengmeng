module
public import Linear.SmoothCoordinateSplit
public import Linear.PolynomialSmoothCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem formalPolynomialAtPoint_coordinate_equiv {K σ τ : Type*} [Field K]
    [Finite σ] [Finite τ] (e : τ ≃ σ) (x : σ → K) (G : MvPolynomial σ K) :
    MvPowerSeries.rename e.symm (formalPolynomialAtPoint x G) =
      formalPolynomialAtPoint (x ∘ e) (MvPolynomial.rename e.symm G) := by
  induction G using MvPolynomial.induction_on with
  | C a => simp [formalPolynomialAtPoint_C]
  | add G H hG hH => simp only [map_add, hG, hH]
  | mul_X G i hG =>
    simp only [map_mul, MvPolynomial.rename_X, hG, formalPolynomialAtPoint_X,
      map_add, MvPowerSeries.rename_X, MvPowerSeries.rename_C,
      Function.comp_apply, Equiv.apply_symm_apply]

theorem reindexed_formal_ideal_of_local_generators
    {K σ τ ι : Type*} [Field K] [Finite σ] [Finite τ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (e : τ ≃ σ) (G : ι → MvPolynomial σ K)
    (hs : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i)))) :
    (I.map (MvPolynomial.rename e.symm).toRingHom).map
      (formalPolynomialAtPoint (x ∘ e)) =
      Ideal.span (Set.range (fun i =>
        formalPolynomialAtPoint (x ∘ e) (MvPolynomial.rename e.symm (G i)))) := by
  have h := congrArg (fun J : Ideal (MvPowerSeries σ K) =>
    J.map (MvPowerSeries.rename e.symm).toRingHom)
    (formalPolynomialIdeal_local_generators I P x hP G hs)
  rw [Ideal.map_map, Ideal.map_span, ← Set.range_comp] at h
  have hc : (MvPowerSeries.rename e.symm).toRingHom.comp (formalPolynomialAtPoint x) =
      (formalPolynomialAtPoint (x ∘ e)).comp (MvPolynomial.rename e.symm).toRingHom := by
    apply RingHom.ext
    intro F
    exact formalPolynomialAtPoint_coordinate_equiv e x F
  rw [hc, ← Ideal.map_map] at h
  have hf : ((MvPowerSeries.rename e.symm).toRingHom ∘
      fun i => formalPolynomialAtPoint x (G i)) =
      (fun i => formalPolynomialAtPoint (x ∘ e) (MvPolynomial.rename e.symm (G i))) := by
    funext i
    exact formalPolynomialAtPoint_coordinate_equiv e x (G i)
  rw [hf] at h
  exact h

theorem reindexed_smooth_formal_ideal
    {K σ : Type*} [Field K] [Finite σ] {r c : ℕ} [Nonempty (Fin c)]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (e : (Fin r ⊕ Fin c) ≃ σ) (G : Fin c → MvPolynomial σ K)
    (hG : ∀ i, MvPolynomial.eval (x ∘ e) (MvPolynomial.rename e.symm (G i)) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval (x ∘ e)
      (MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.rename e.symm (G i))))))
    (hs : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i)))) :
    I.map ((polynomialSmoothFormalMap (x ∘ e) (fun i => MvPolynomial.rename e.symm (G i))
        hG hJ).comp (MvPolynomial.rename e.symm).toRingHom) =
      Ideal.span (Set.range
        (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))) := by
  rw [← Ideal.map_map]
  exact polynomialSmoothFormalMap_ideal _ _ _ hG hJ
    (reindexed_formal_ideal_of_local_generators I P x hP e G hs)

/-- A genuine formal normal-ideal presentation, derived from smoothness and
the original embedded ideal. Nonzero local ideal excludes codimension zero. -/
theorem smooth_point_has_formal_normal_coordinates
    {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (hI : I.map (algebraMap _ (Localization.AtPrime P)) ≠ ⊥)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    ∃ (r c : ℕ) (hc : 0 < c),
      letI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
      ∃ (e : (Fin r ⊕ Fin c) ≃ σ) (G : Fin c → MvPolynomial σ K)
        (hG : ∀ i, MvPolynomial.eval (x ∘ e) (MvPolynomial.rename e.symm (G i)) = 0)
        (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval (x ∘ e)
          (MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.rename e.symm (G i)))))),
        I.map ((polynomialSmoothFormalMap (x ∘ e)
          (fun i => MvPolynomial.rename e.symm (G i)) hG hJ).comp
          (MvPolynomial.rename e.symm).toRingHom) =
            Ideal.span (Set.range
              (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))) := by
  obtain ⟨r, c, e, G, hs, hG, hJ⟩ :=
    smooth_generators_exist_with_normal_coordinate_minor I P hIP x hP
  have hc : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc
    subst c
    apply hI
    simpa using hs
  refine ⟨r, c, hc, ?_⟩
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  exact ⟨e, G, hG, hJ, reindexed_smooth_formal_ideal I P x hP e G hG hJ hs⟩

end LinearStudy
