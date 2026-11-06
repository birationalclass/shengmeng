module
public import Linear.HomogeneousRationalPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogeneous generators with invertible scalar changes give the same
actual mapped ideal. The scalar is allowed to depend on the generator. -/
theorem homogeneous_ideal_maps_eq_of_unit_scaling
    {K σ S : Type*} [Field K] [CommRing S]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (φ ψ : MvPolynomial σ K →+* S)
    (hscale : ∀ H : MvPolynomial σ K, ∀ m : ℕ, H.IsHomogeneous m →
      ∃ u : Sˣ, φ H = u * ψ H) : I.map φ = I.map ψ := by
  classical
  obtain ⟨G, hG⟩ := (Ideal.IsHomogeneous.iff_exists
    (MvPolynomial.homogeneousSubmodule σ K) I).mp hI
  have hmem : ∀ H ∈ ((↑) '' G : Set (MvPolynomial σ K)),
      ∀ J : Ideal S, φ H ∈ J ↔ ψ H ∈ J := by
    rintro H ⟨h, hh, rfl⟩ J
    obtain ⟨m, hm⟩ := h.property
    obtain ⟨u, hu⟩ := hscale h m hm
    rw [hu]
    exact J.unit_mul_mem_iff_mem u.isUnit
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    rw [hG]
    apply Ideal.span_le.mpr
    intro H hH
    exact (hmem H hH _).mpr
      (Ideal.mem_map_of_mem ψ (hG ▸ Ideal.subset_span hH))
  · apply Ideal.map_le_iff_le_comap.mpr
    rw [hG]
    apply Ideal.span_le.mpr
    intro H hH
    exact (hmem H hH _).mp
      (Ideal.mem_map_of_mem φ (hG ▸ Ideal.subset_span hH))

theorem homogeneous_projective_chart_pullback_ideal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) :
    let D := affineChartPolynomialMap (K := K) (n := n)
    let p0 := D (F 0)
    let p := fun i : Fin n => D (F i.succ)
    (I.map D.toRingHom).map (rationalPolynomialChartMap p0 p).toRingHom =
      (I.map (MvPolynomial.aeval F).toRingHom).map
        ((algebraMap _ (Localization.Away p0)).comp D.toRingHom) := by
  intro D p0 p
  rw [Ideal.map_map, Ideal.map_map]
  apply homogeneous_ideal_maps_eq_of_unit_scaling I hI
  intro H m hm
  have hu : IsUnit (IsLocalization.Away.invSelf p0 (S := Localization.Away p0)) := by
    exact IsUnit.of_mul_eq_one_right
      (algebraMap _ (Localization.Away p0) p0) (IsLocalization.Away.mul_invSelf p0)
  refine ⟨(hu.pow m).unit, ?_⟩
  rw [IsUnit.unit_spec]
  change rationalPolynomialChartMap p0 p (D H) =
    IsLocalization.Away.invSelf p0 ^ m *
      algebraMap _ (Localization.Away p0) (D (MvPolynomial.aeval F H))
  rw [homogeneous_rational_chart_pullback p0 p H hm]
  congr 1
  have he : ((IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K)
      (Localization.Away p0)).comp D).comp (MvPolynomial.aeval F) =
      MvPolynomial.aeval (Fin.cases (algebraMap _ (Localization.Away p0) p0)
        (fun i => algebraMap _ (Localization.Away p0) (p i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;> simp [p0, p]
  exact (AlgHom.congr_fun he H).symm

end LinearStudy
