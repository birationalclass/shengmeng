module
public import Linear.PolynomialSmoothCoordinates
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem ideal_generators_of_conormal_span {R ι : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤)
    (G : ι → I)
    (hG : Submodule.span R (Set.range (fun i => I.toCotangent (G i))) = ⊤) :
    Ideal.span (Set.range (fun i => (G i : R))) = I := by
  let N : Submodule R I := Submodule.span R (Set.range G)
  have hm : N.map I.toCotangent = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact hG
  have hc := congrArg (Submodule.comap I.toCotangent) hm
  rw [Submodule.comap_map_eq, Submodule.comap_top] at hc
  have hh := congrArg (Submodule.map I.subtype) hc
  rw [Submodule.map_sup, I.map_toCotangent_ker, Submodule.map_top,
    Submodule.range_subtype] at hh
  have hspan : N.map I.subtype = Ideal.span (Set.range (fun i => (G i : R))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hspan] at hh
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (G i).property
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I)
      ((IsLocalRing.le_maximalIdeal hI).trans (IsLocalRing.maximalIdeal_le_jacobson _))
    rw [smul_eq_mul, ← pow_two]
    exact hh.symm.le

theorem ideal_generators_of_conormal_quotient_span {R ι : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤)
    (G : ι → I)
    (hG : Submodule.span (R ⧸ I) (Set.range (fun i => I.toCotangent (G i))) = ⊤) :
    Ideal.span (Set.range (fun i => (G i : R))) = I := by
  apply ideal_generators_of_conormal_span I hI G
  rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective,
    hG, Submodule.restrictScalars_top]

theorem exists_ideal_generators_of_conormal_basis {R ι : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤)
    (b : Module.Basis ι (R ⧸ I) I.Cotangent) :
    ∃ G : ι → I, (∀ i, I.toCotangent (G i) = b i) ∧
      Ideal.span (Set.range (fun i => (G i : R))) = I := by
  choose G hG using fun i => I.toCotangent_surjective (b i)
  refine ⟨G, hG, ideal_generators_of_conormal_quotient_span I hI G ?_⟩
  simp_rw [hG]
  exact b.span_eq

theorem span_unit_scaled_family {R ι : Type*} [CommRing R] (G : ι → R)
    (u : ι → Rˣ) :
    Ideal.span (Set.range (fun i => (u i : R) * G i)) = Ideal.span (Set.range G) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ Ideal.mem_span_range_self
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : (u i : R) * G i ∈ Ideal.span (Set.range (fun j => (u j : R) * G j)) :=
      Ideal.mem_span_range_self
    simpa [mul_assoc] using
      (Ideal.span (Set.range (fun j => (u j : R) * G j))).mul_mem_left
        ((u i)⁻¹ : Rˣ) hi

theorem exists_polynomial_local_generators_of_conormal_basis
    {K σ ι : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P)
    (b : Module.Basis ι
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))
      (I.map (algebraMap _ (Localization.AtPrime P))).Cotangent) :
    ∃ G : ι → MvPolynomial σ K,
      I.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))) := by
  let S := Localization.AtPrime P
  let J := I.map (algebraMap _ S)
  have hJ : J ≠ ⊤ := by
    have hle : J ≤ IsLocalRing.maximalIdeal S := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hIP
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hle
  obtain ⟨T, hT, hspan⟩ := exists_ideal_generators_of_conormal_basis J hJ b
  choose a hs using fun i => IsLocalization.surj P.primeCompl (T i : S)
  let s := fun i => (a i).2
  let u : ι → Sˣ := fun i => (IsLocalization.map_units S (s i)).unit
  have hu : ∀ i, (u i : S) = algebraMap (MvPolynomial σ K) S (s i) :=
    fun i => IsUnit.unit_spec _
  refine ⟨fun i => (a i).1, ?_⟩
  change J = _
  rw [← hspan, ← span_unit_scaled_family (fun i => (T i : S)) u]
  congr 2
  funext i
  rw [hu, mul_comm]
  exact hs i

end LinearStudy
