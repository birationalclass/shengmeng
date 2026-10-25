module
public import Linear.PolynomialFirstJet
public import Linear.FirstOrderLocalParameters
public import Linear.SmoothCotangentDimension
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K] [Finite σ]

theorem polynomial_point_kernel_eq_span_centered_coordinates (x : σ → K) :
    RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom =
      Ideal.span (Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (x i))) := by
  let E := polynomialTranslation x
  have hmap : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).map E.toRingHom =
      MvPolynomial.idealOfVars σ K := by
    rw [← polynomialTranslation_origin_kernel x]
    exact Ideal.map_comap_of_surjective E.toRingHom E.surjective _
  have hs : (Ideal.span (Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (x i)))).map
      E.toRingHom = MvPolynomial.idealOfVars σ K := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    ext F
    simp [Function.comp_def, E, polynomialTranslation]
  have h := congrArg (fun J : Ideal (MvPolynomial σ K) => J.comap E.toRingHom)
    (hmap.trans hs.symm)
  simpa only [Ideal.comap_map_of_bijective E.toRingHom E.bijective] using h

theorem polynomial_firstOrder_normal_pointIdeal
    {α β : Type*} [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    (x : α ⊕ β → K) (G : β → MvPolynomial (α ⊕ β) K)
    (h0 : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hD : ∀ i j, MvPolynomial.eval x (MvPolynomial.pderiv j (G i)) =
      if j = Sum.inr i then 1 else 0) :
    ∀ i, G i - (MvPolynomial.X (Sum.inr i) - MvPolynomial.C (x (Sum.inr i))) ∈
      (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) ^ 2 := by
  classical
  intro i
  apply polynomial_zero_firstJet_mem_point_square
  · simp [h0 i]
  · intro j
    simp [hD i j, MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

/-- Actual centered tangent polynomials generate the target point's local
quotient maximal ideal when actual local equations have the standard first jet. -/
theorem polynomial_firstOrder_tangents_generate_local_quotient
    {α β : Type*} [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    (I P : Ideal (MvPolynomial (α ⊕ β) K)) [P.IsPrime] (hIP : I ≤ P)
    (x : α ⊕ β → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : β → MvPolynomial (α ⊕ β) K)
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (h0 : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hD : ∀ i j, MvPolynomial.eval x (MvPolynomial.pderiv j (G i)) =
      if j = Sum.inr i then 1 else 0) :
    let J := I.map (algebraMap _ (Localization.AtPrime P))
    letI : Nontrivial (Localization.AtPrime P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
      (polynomial_local_ideal_ne_top I P hIP)
    letI : IsLocalRing (Localization.AtPrime P ⧸ J) := IsLocalRing.of_surjective'
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    Ideal.span (Set.range (fun i : α => Ideal.Quotient.mk J
      (algebraMap (MvPolynomial (α ⊕ β) K) (Localization.AtPrime P)
        (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (x (Sum.inl i)))))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P ⧸ J) := by
  let J := I.map (algebraMap _ (Localization.AtPrime P))
  let : Nontrivial (Localization.AtPrime P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I P hIP)
  let : IsLocalRing (Localization.AtPrime P ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let v := fun i => algebraMap _ (Localization.AtPrime P)
    (MvPolynomial.X i - MvPolynomial.C (x i))
  have hv : Ideal.span (Set.range v) = IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    have hPk := hP.trans (polynomial_point_kernel_eq_span_centered_coordinates x)
    have hh := congrArg (fun J : Ideal (MvPolynomial (α ⊕ β) K) =>
      J.map (algebraMap _ (Localization.AtPrime P))) hPk
    rw [Ideal.map_span, ← Set.range_comp] at hh
    exact hh.symm.trans Localization.AtPrime.map_eq_maximalIdeal
  have hJ : J ≤ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hIP
  have hG : ∀ i, algebraMap _ (Localization.AtPrime P) (G i) ∈ J := by
    intro i
    dsimp only [J]
    rw [hlocal]
    exact Ideal.mem_span_range_self (x := i)
  have hfirst : ∀ i, algebraMap _ (Localization.AtPrime P) (G i) - v (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 2 := by
    intro i
    have hh := Ideal.mem_map_of_mem (algebraMap _ (Localization.AtPrime P))
      (polynomial_firstOrder_normal_pointIdeal x G h0 hD i)
    rw [← hP, Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal] at hh
    simpa only [map_sub, v] using hh
  exact firstOrder_tangents_generate_quotient_maximalIdeal J hJ v hv _ hG hfirst
end LinearStudy
