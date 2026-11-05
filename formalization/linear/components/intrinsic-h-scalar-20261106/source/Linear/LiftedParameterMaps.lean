module
public import Linear.LiftedParameterCoordinates
public import Linear.PowerSeriesCoefficients
public import Linear.PowerSeriesCentering
public import Linear.CompleteIntersectionChange
public import Linear.Target

/-! Actual coordinate and quotient maps for arbitrary parameter lifts, including coefficient-field preservation and compatibility with a constructed base automorphism. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace LinearStudy
theorem powerSeries_ringEnd_bijective_of_parameter_images
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : MvPowerSeries ι K →+* MvPowerSeries ι K)
    (hX : Ideal.span (Set.range (fun i => f (MvPowerSeries.X i))) =
      IsLocalRing.maximalIdeal (MvPowerSeries ι K))
    (hC : ∀ k : K, f (MvPowerSeries.C k) = MvPowerSeries.C k) : Function.Bijective f := by
  let I : Ideal (MvPowerSeries ι K) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : I.map f = I := by
    rw [Ideal.map_span, ← Set.range_comp]
    change Ideal.span (Set.range (fun i => f (MvPowerSeries.X i))) = I
    rw [hX]
    exact powerSeries_coordinateIdeal_eq_maximalIdeal.symm
  have : IsHausdorff (I.map f) (MvPowerSeries ι K) := by rw [hmap]; infer_instance
  have hsur : Function.Surjective f := by
    apply surjective_of_mk_map_comp_surjective (I := I) f
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPowerSeries.C a.constantCoeff, ?_⟩
    change Ideal.Quotient.mk (I.map f) (f (MvPowerSeries.C a.constantCoeff)) = _
    rw [hC, Ideal.Quotient.eq, hmap]
    change MvPowerSeries.C a.constantCoeff - a ∈ Ideal.span (Set.range MvPowerSeries.X)
    rw [← powerSeries_constantCoeff_kernel]
    change (MvPowerSeries.C a.constantCoeff - a).constantCoeff = 0
    simp
  exact ⟨noetherian_ringEnd_injective_of_surjective f hsur, hsur⟩

theorem liftedParameterCoordinateEquiv_constant
    {K : Type*} [Field K] {r c : ℕ} (hc : 0 < c)
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) (k : K) :
    liftedParameterCoordinateEquiv hc P hP (MvPowerSeries.C (MvPowerSeries.C k)) =
      MvPowerSeries.C (MvPowerSeries.C k) := by
  let : Nonempty (Fin r ⊕ Fin c) := ⟨Sum.inr ⟨0, hc⟩⟩
  apply (powerSeriesCoordinateChart K r c).injective
  change powerSeriesCoordinateChart K r c
    ((powerSeriesCoordinateChart K r c).symm
      (parameterSubstitutionEquiv (liftedCoordinateImages P)
        (liftedCoordinateImages_span hc P hP)
          (powerSeriesCoordinateChart K r c (MvPowerSeries.C (MvPowerSeries.C k))))) = _
  rw [RingEquiv.apply_symm_apply, powerSeriesCoordinateChart_C, MvPowerSeries.rename_C]
  exact (parameterSubstitutionEquiv (liftedCoordinateImages P)
    (liftedCoordinateImages_span hc P hP)).commutes k

theorem liftedParameterMap_constant
    {K : Type*} [Field K] {r c : ℕ} (hc : 0 < c)
    (I : Ideal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)))
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) (k : K) :
    liftedParameterMap I hc P hP (MvPowerSeries.C k) =
      algebraMap (MvPowerSeries (Fin r) K)
        (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ I) (MvPowerSeries.C k) := by
  change Ideal.Quotient.mk I
    (liftedParameterCoordinateEquiv hc P hP (MvPowerSeries.C (MvPowerSeries.C k))) =
      Ideal.Quotient.mk I (MvPowerSeries.C (MvPowerSeries.C k))
  rw [liftedParameterCoordinateEquiv_constant]

theorem centered_powerSeries_retraction_eq_constantCoeff
    {B ι : Type*} [CommRing B] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : MvPowerSeries ι B →ₐ[B] B) (ha : ∀ i, a (MvPowerSeries.X i) = 0)
    (f : MvPowerSeries ι B) : a f = f.constantCoeff := by
  have hker : RingHom.ker (MvPowerSeries.constantCoeff (σ := ι) (R := B)) ≤
      RingHom.ker a.toRingHom := by
    rw [powerSeries_constantCoeff_kernel]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ha i
  have hd : f - MvPowerSeries.C f.constantCoeff ∈
      RingHom.ker (MvPowerSeries.constantCoeff (σ := ι) (R := B)) := by
    change (f - MvPowerSeries.C f.constantCoeff).constantCoeff = 0
    rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have h := hker hd
  change a (f - MvPowerSeries.C f.constantCoeff) = 0 at h
  have hc : a (MvPowerSeries.C f.constantCoeff) = f.constantCoeff := a.commutes _
  rw [map_sub, hc] at h
  exact sub_eq_zero.mp h
theorem centered_lifts_parameter_map_exists
    {K : Type*} [Field K] {r c : ℕ} (hc : 0 < c)
    (I : Ideal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)))
    (q : (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ I) →ₐ[MvPowerSeries (Fin r) K]
      MvPowerSeries (Fin r) K)
    (hq : ∀ j : Fin c, q (Ideal.Quotient.mk I (MvPowerSeries.X j)) = 0)
    (tau : Fin r → (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ I))
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) :
    ∃ phi : MvPowerSeries (Fin r) K →+*
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ I),
        (∀ i, phi (MvPowerSeries.X i) = tau i) ∧
        ∀ k : K, phi (MvPowerSeries.C k) =
          algebraMap (MvPowerSeries (Fin r) K)
            (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ I) (MvPowerSeries.C k) := by
  classical
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  choose P hP using fun i => Ideal.Quotient.mk_surjective (tau i)
  let a := q.comp (Ideal.Quotient.mkₐ (MvPowerSeries (Fin r) K) I)
  have hcc : (fun i => (P i).constantCoeff) = (fun i => q (tau i)) := by
    funext i
    have he := centered_powerSeries_retraction_eq_constantCoeff a hq (P i)
    change q (Ideal.Quotient.mk I (P i)) = (P i).constantCoeff at he
    rw [hP] at he
    exact he.symm
  have hgen : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) := by
    rw [hcc]
    exact htau
  refine ⟨liftedParameterMap I hc P hgen, ?_, ?_⟩
  · intro i
    rw [liftedParameterMap_X, hP]
  · exact liftedParameterMap_constant hc I P hgen
theorem completeIntersection_lifted_parameter_map_exists
    {r c : ℕ} (H : Fin c → AmbientRing r c) (hc : 0 < c)
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    ∃ phi : ParameterRing r →+* CompleteIntersection H,
      (∀ i, phi (MvPowerSeries.X i) = tau i) ∧
      ∀ k : ℂ, phi (MvPowerSeries.C k) =
        algebraMap (ParameterRing r) (CompleteIntersection H) (MvPowerSeries.C k) := by
  dsimp only [CompleteIntersection, equationIdeal, AmbientRing, ParameterRing] at *
  let B := ParameterRing r
  let R := AmbientRing r c
  let I := Ideal.span (Set.range H)
  let aR : R →ₐ[B] B := q.comp (Ideal.Quotient.mkₐ B I)
  let e := powerSeriesCentering aR
  let H' := fun i => e.symm (H i)
  let I' := Ideal.span (Set.range H')
  let E : (R ⧸ I') ≃ₐ[B] (R ⧸ I) := (equationChangeQuotientEquiv e.symm H).symm
  let q' : (R ⧸ I') →ₐ[B] B := q.comp E.toAlgHom
  let tau' : Fin r → (R ⧸ I') := fun i => E.symm (tau i)
  have hmk (z : R) : E (Ideal.Quotient.mk I' z) = Ideal.Quotient.mk I (e z) := by
    apply (equationChangeQuotientEquiv e.symm H).injective
    rw [AlgEquiv.apply_symm_apply, equationChangeQuotientEquiv_mk,
      AlgEquiv.symm_apply_apply]
  have hz (i : Fin c) : q' (Ideal.Quotient.mk I' (MvPowerSeries.X i)) = 0 := by
    change q (E (Ideal.Quotient.mk I' (MvPowerSeries.X i))) = 0
    rw [hmk]
    exact powerSeriesCentering_coordinate_reduction_zero aR i
  have hgen : Ideal.span (Set.range (fun i => q' (tau' i))) =
      IsLocalRing.maximalIdeal B := by
    have hf : (fun i => q' (tau' i)) = (fun i => q (tau i)) := by
      funext i
      change q (E (E.symm (tau i))) = q (tau i)
      rw [AlgEquiv.apply_symm_apply]
    rw [hf]
    exact htau
  obtain ⟨phi, hphi, hconst⟩ := centered_lifts_parameter_map_exists hc I' q' hz tau' hgen
  refine ⟨E.toRingEquiv.toRingHom.comp phi, ?_, ?_⟩
  · intro i
    change E (phi (MvPowerSeries.X i)) = tau i
    rw [hphi]
    exact E.apply_symm_apply _
  · intro k
    change E (phi (MvPowerSeries.C k)) = _
    rw [hconst]
    exact E.commutes _
theorem completeIntersection_lifted_parameter_map_compatible
    {r c : ℕ} (H : Fin c → AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    ∃ phi : ParameterRing r →+* CompleteIntersection H,
      ∃ alpha : ParameterRing r ≃+* ParameterRing r,
        (∀ i, phi (MvPowerSeries.X i) = tau i) ∧
        (∀ k : ℂ, phi (MvPowerSeries.C k) =
          algebraMap (ParameterRing r) (CompleteIntersection H) (MvPowerSeries.C k)) ∧
        ∀ b, q (phi b) = alpha b := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨phi, hphi, hC⟩ := completeIntersection_lifted_parameter_map_exists H hc q tau htau
  let f := q.toRingHom.comp phi
  have hX : Ideal.span (Set.range (fun i => f (MvPowerSeries.X i))) =
      IsLocalRing.maximalIdeal (ParameterRing r) := by
    have hf : (fun i => f (MvPowerSeries.X i)) = (fun i => q (tau i)) := by
      funext i
      change q (phi (MvPowerSeries.X i)) = _
      rw [hphi]
    rw [hf]
    exact htau
  have hconst : ∀ k : ℂ, f (MvPowerSeries.C k) = MvPowerSeries.C k := by
    intro k
    change q (phi (MvPowerSeries.C k)) = _
    rw [hC, q.commutes]
    rfl
  let alpha := RingEquiv.ofBijective f (powerSeries_ringEnd_bijective_of_parameter_images f hX hconst)
  exact ⟨phi, alpha, hphi, hC, fun _ => rfl⟩

theorem completeIntersection_lifted_coordinate_equiv_exists
    {r c : ℕ} (H : Fin c → AmbientRing r c) (hc : 0 < c)
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    ∃ e : AmbientRing r c ≃+* AmbientRing r c,
      (∀ i, Ideal.Quotient.mk (equationIdeal H) (e (MvPowerSeries.C (MvPowerSeries.X i))) = tau i) ∧
      ∀ k : ℂ, e (MvPowerSeries.C (MvPowerSeries.C k)) = MvPowerSeries.C (MvPowerSeries.C k) := by
  classical
  dsimp only [CompleteIntersection, equationIdeal, AmbientRing, ParameterRing] at *
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  let B := ParameterRing r
  let R := AmbientRing r c
  let I := Ideal.span (Set.range H)
  let aR : R →ₐ[B] B := q.comp (Ideal.Quotient.mkₐ B I)
  let e0 := powerSeriesCentering aR
  let H' := fun i => e0.symm (H i)
  let I' := Ideal.span (Set.range H')
  let E : (R ⧸ I') ≃ₐ[B] (R ⧸ I) := (equationChangeQuotientEquiv e0.symm H).symm
  let q' := q.comp E.toAlgHom
  let tau' := fun i => E.symm (tau i)
  have hmk (z : R) : E (Ideal.Quotient.mk I' z) = Ideal.Quotient.mk I (e0 z) := by
    apply (equationChangeQuotientEquiv e0.symm H).injective
    rw [AlgEquiv.apply_symm_apply, equationChangeQuotientEquiv_mk, AlgEquiv.symm_apply_apply]
  have hz (i : Fin c) : q' (Ideal.Quotient.mk I' (MvPowerSeries.X i)) = 0 := by
    change q (E (Ideal.Quotient.mk I' (MvPowerSeries.X i))) = 0
    rw [hmk]
    exact powerSeriesCentering_coordinate_reduction_zero aR i
  choose P hP using fun i => Ideal.Quotient.mk_surjective (tau' i)
  let a := q'.comp (Ideal.Quotient.mkₐ B I')
  have hcc : (fun i => (P i).constantCoeff) = (fun i => q (tau i)) := by
    funext i
    have he := centered_powerSeries_retraction_eq_constantCoeff a hz (P i)
    change q (E (Ideal.Quotient.mk I' (P i))) = (P i).constantCoeff at he
    rw [hP] at he
    change q (E (E.symm (tau i))) = _ at he
    rw [E.apply_symm_apply] at he
    exact he.symm
  have hgen : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal B := by rw [hcc]; exact htau
  let e1 := liftedParameterCoordinateEquiv hc P hgen
  refine ⟨e1.trans e0.toRingEquiv, ?_, ?_⟩
  · intro i
    change Ideal.Quotient.mk I (e0 (e1 (MvPowerSeries.C (MvPowerSeries.X i)))) = _
    rw [liftedParameterCoordinateEquiv_parameter, ← hmk, hP]
    exact E.apply_symm_apply _
  · intro k
    change e0 (e1 (MvPowerSeries.C (MvPowerSeries.C k))) = _
    rw [liftedParameterCoordinateEquiv_constant]
    exact e0.commutes (MvPowerSeries.C k)
end LinearStudy
