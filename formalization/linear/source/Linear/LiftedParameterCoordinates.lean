module
public import Linear.ParameterSubstitution
public import Linear.PowerSeriesCoordinateChart
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Data.Fintype.Sum

@[expose] public section
/-! Construct a genuine nested power-series coordinate automorphism and quotient algebra action from representatives whose constant coefficients generate the parameter maximal ideal. Compatibility with reduction and finite freeness under this new action are not claimed here. -/
noncomputable section
namespace LinearStudy
theorem nested_lifted_parameter_ideal
    {K : Type*} [Field K] {r c : ℕ}
    (hc : 0 < c)
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) :
    Ideal.span (Set.range P ∪ Set.range (MvPowerSeries.X (R := MvPowerSeries (Fin r) K)
      (σ := Fin c))) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) := by
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  let B := MvPowerSeries (Fin r) K
  let R := MvPowerSeries (Fin c) B
  let cc : R →+* B := MvPowerSeries.constantCoeff
  let J : Ideal R := Ideal.span (Set.range P ∪ Set.range MvPowerSeries.X)
  have hker : RingHom.ker cc ≤ J := by
    rw [powerSeries_constantCoeff_kernel]
    exact Ideal.span_mono Set.subset_union_right
  have hmap : J.map cc = IsLocalRing.maximalIdeal B := by
    dsimp only [J]
    rw [Ideal.span_union, Ideal.map_sup, Ideal.map_span, Ideal.map_span]
    rw [← Set.range_comp, ← Set.range_comp]
    have hx : cc ∘ MvPowerSeries.X = (fun _ : Fin c => (0 : B)) := by
      funext i
      exact MvPowerSeries.constantCoeff_X i
    rw [hx]
    have hz : Ideal.span (Set.range (fun _ : Fin c => (0 : B))) = ⊥ := by
      apply bot_unique
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.zero_mem _
    rw [hz]
    simpa only [sup_bot_eq, cc, Function.comp_def] using hP
  have heq : J = (IsLocalRing.maximalIdeal B).comap cc := by
    rw [← hmap, Ideal.comap_map_of_surjective cc (by
      intro b
      exact ⟨MvPowerSeries.C b, MvPowerSeries.constantCoeff_C b⟩)]
    exact (sup_eq_left.mpr hker).symm
  change J = IsLocalRing.maximalIdeal R
  rw [heq]
  ext f
  change ¬ IsUnit f.constantCoeff ↔ ¬ IsUnit f
  exact not_congr (show IsUnit f ↔ IsUnit f.constantCoeff from
    MvPowerSeries.isUnit_iff_constantCoeff).symm

def liftedCoordinateImages {K : Type*} [Field K] {r c : ℕ}
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    Fin r ⊕ Fin c → MvPowerSeries (Fin r ⊕ Fin c) K :=
  Sum.elim (fun i => powerSeriesCoordinateChart K r c (P i))
    (fun j => MvPowerSeries.X (Sum.inr j))

theorem liftedCoordinateImages_span {K : Type*} [Field K] {r c : ℕ}
    (hc : 0 < c)
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) :
    Ideal.span (Set.range (liftedCoordinateImages P)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) K) := by
  have hrange : Set.range (liftedCoordinateImages P) =
      (powerSeriesCoordinateChart K r c) ''
        (Set.range P ∪ Set.range MvPowerSeries.X) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact ⟨P i, Or.inl (Set.mem_range_self i), rfl⟩
      | inr i => exact ⟨MvPowerSeries.X i, Or.inr (Set.mem_range_self i),
          powerSeriesCoordinateChart_X K r c i⟩
    · rintro ⟨f, hf, rfl⟩
      rcases hf with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr i, (powerSeriesCoordinateChart_X K r c i).symm⟩
  rw [hrange, ← Ideal.map_span, nested_lifted_parameter_ideal hc P hP]
  exact IsLocalRing.map_ringEquiv_maximalIdeal (powerSeriesCoordinateChart K r c)
def liftedParameterCoordinateEquiv {K : Type*} [Field K] {r c : ℕ}
    (hc : 0 < c)
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) :
    MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ≃+*
      MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) := by
  let : Nonempty (Fin r ⊕ Fin c) := ⟨Sum.inr ⟨0, hc⟩⟩
  exact (powerSeriesCoordinateChart K r c).trans
    ((parameterSubstitutionEquiv (liftedCoordinateImages P)
      (liftedCoordinateImages_span hc P hP)).toRingEquiv.trans
        (powerSeriesCoordinateChart K r c).symm)

theorem liftedParameterCoordinateEquiv_parameter {K : Type*} [Field K] {r c : ℕ}
    (hc : 0 < c)
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) (i : Fin r) :
    liftedParameterCoordinateEquiv hc P hP (MvPowerSeries.C (MvPowerSeries.X i)) = P i := by
  let : Nonempty (Fin r ⊕ Fin c) := ⟨Sum.inr ⟨0, hc⟩⟩
  apply (powerSeriesCoordinateChart K r c).injective
  change powerSeriesCoordinateChart K r c
    ((powerSeriesCoordinateChart K r c).symm
      (parameterSubstitutionEquiv (liftedCoordinateImages P)
        (liftedCoordinateImages_span hc P hP)
          (powerSeriesCoordinateChart K r c (MvPowerSeries.C (MvPowerSeries.X i))))) = _
  rw [RingEquiv.apply_symm_apply, powerSeriesCoordinateChart_C, MvPowerSeries.rename_X,
    parameterSubstitutionEquiv_X]
  rfl

theorem liftedParameterCoordinateEquiv_normal {K : Type*} [Field K] {r c : ℕ}
    (hc : 0 < c)
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) (i : Fin c) :
    liftedParameterCoordinateEquiv hc P hP (MvPowerSeries.X i) = MvPowerSeries.X i := by
  let : Nonempty (Fin r ⊕ Fin c) := ⟨Sum.inr ⟨0, hc⟩⟩
  apply (powerSeriesCoordinateChart K r c).injective
  change powerSeriesCoordinateChart K r c
    ((powerSeriesCoordinateChart K r c).symm
      (parameterSubstitutionEquiv (liftedCoordinateImages P)
        (liftedCoordinateImages_span hc P hP)
          (powerSeriesCoordinateChart K r c (MvPowerSeries.X i)))) = _
  rw [RingEquiv.apply_symm_apply, powerSeriesCoordinateChart_X, parameterSubstitutionEquiv_X]
  rfl
def liftedParameterMap {K : Type*} [Field K] {r c : ℕ}
    (I : Ideal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))) (hc : 0 < c)
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) :
    MvPowerSeries (Fin r) K →+*
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ I) :=
  (Ideal.Quotient.mk I).comp
    ((liftedParameterCoordinateEquiv hc P hP).toRingHom.comp MvPowerSeries.C)

@[instance_reducible] def liftedParameterAlgebra {K : Type*} [Field K] {r c : ℕ}
    (I : Ideal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))) (hc : 0 < c)
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) :
    Algebra (MvPowerSeries (Fin r) K)
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ I) :=
  (liftedParameterMap I hc P hP).toAlgebra

theorem liftedParameterMap_X {K : Type*} [Field K] {r c : ℕ}
    (I : Ideal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))) (hc : 0 < c)
    (P : Fin r → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (hP : Ideal.span (Set.range (fun i => (P i).constantCoeff)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) (i : Fin r) :
    liftedParameterMap I hc P hP (MvPowerSeries.X i) = Ideal.Quotient.mk I (P i) := by
  change Ideal.Quotient.mk I
    (liftedParameterCoordinateEquiv hc P hP (MvPowerSeries.C (MvPowerSeries.X i))) = _
  rw [liftedParameterCoordinateEquiv_parameter]
end LinearStudy
