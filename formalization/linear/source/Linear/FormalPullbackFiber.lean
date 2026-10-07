module
public import Linear.FormalFirstOrder
public import Linear.SmoothPolynomialFiber
public import Linear.FormalParameterFiber
public import Linear.SmoothNormalJacobian
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

theorem formal_target_parameter_span
    (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hH : ∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) K)) ^ 2) :
    Ideal.span (Set.range (smoothCoordinateImages H)) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) K) := by
  obtain ⟨E, hp, hn⟩ := normal_firstOrder_formal_coordinate_exists H hH
  have he : (E.toRingEquiv.toRingHom ∘ MvPowerSeries.X) = smoothCoordinateImages H := by
    funext i
    cases i with
    | inl i => simpa [smoothCoordinateImages] using hp (MvPowerSeries.X i)
    | inr i => exact hn i
  rw [← he, Set.range_comp, ← Ideal.map_span,
    powerSeries_coordinateIdeal_eq_maximalIdeal]
  exact IsLocalRing.map_ringEquiv_maximalIdeal E.toRingEquiv

theorem formal_pullback_full_fiber_ideal
    (v : Fin r ⊕ Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hv : ∀ i, (v i).constantCoeff = 0)
    (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hH : ∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) K)) ^ 2) :
    Ideal.span (Set.range (fun i => v (Sum.inl i))) ⊔
      Ideal.span (Set.range (fun i => MvPowerSeries.substAlgHom
        (MvPowerSeries.hasSubst_of_constantCoeff_zero hv) (H i))) =
      Ideal.span (Set.range v) := by
  let φ := (MvPowerSeries.substAlgHom (R := K)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hv)).toRingHom
  have hh := congrArg (Ideal.map φ) (formal_target_parameter_span H hH)
  rw [Ideal.map_span, ← Set.range_comp] at hh
  have hrange : Set.range (φ ∘ smoothCoordinateImages H) =
      Set.range (fun i => v (Sum.inl i)) ∪ Set.range (fun i => φ (H i)) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl ⟨i, (MvPowerSeries.substAlgHom_X _ _).symm⟩
      | inr i => exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Sum.inl i, MvPowerSeries.substAlgHom_X _ _⟩
      · exact ⟨Sum.inr i, rfl⟩
  rw [hrange, Ideal.span_union] at hh
  have hm : (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) K)).map φ =
      Ideal.span (Set.range v) := by
    rw [← powerSeries_coordinateIdeal_eq_maximalIdeal, Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact MvPowerSeries.substAlgHom_X _ i
  rw [hm] at hh
  exact hh

theorem formal_unit_divided_fiber_ideal
    (p : Fin r ⊕ Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hp : ∀ i, (p i).constantCoeff = 0)
    (u : (MvPowerSeries (Fin r ⊕ Fin c) K)ˣ)
    (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hH : ∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) K)) ^ 2) :
    let v := fun i => (u⁻¹ : (MvPowerSeries (Fin r ⊕ Fin c) K)ˣ) * p i
    let hv : ∀ i, (v i).constantCoeff = 0 := by intro i; simp [v, hp i]
    Ideal.span (Set.range (fun i => v (Sum.inl i))) ⊔
      Ideal.span (Set.range (fun i => MvPowerSeries.substAlgHom
        (MvPowerSeries.hasSubst_of_constantCoeff_zero hv) (H i))) =
      Ideal.span (Set.range p) := by
  intro v hv
  exact (formal_pullback_full_fiber_ideal v hv H hH).trans
    (span_unit_inv_scaled_family p u)

theorem formal_unit_divided_transformed_firstOrder {S : Type*} [CommRing S]
    (p : Fin r ⊕ Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hp : ∀ i, (p i).constantCoeff = 0)
    (u : (MvPowerSeries (Fin r ⊕ Fin c) K)ˣ)
    (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hH : ∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) K)) ^ 2)
    (E : MvPowerSeries (Fin r ⊕ Fin c) K →+* S) :
    let v := fun i => (u⁻¹ : (MvPowerSeries (Fin r ⊕ Fin c) K)ˣ) * p i
    let hv : ∀ i, (v i).constantCoeff = 0 := by intro i; simp [v, hp i]
    ∀ i, E (MvPowerSeries.substAlgHom
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hv) (H i)) -
        E (u⁻¹ : (MvPowerSeries (Fin r ⊕ Fin c) K)ˣ) * E (p (Sum.inr i)) ∈
          (Ideal.span (Set.range (fun j => E (p j)))) ^ 2 := by
  intro v hv i
  have h := Ideal.mem_map_of_mem E
    (formal_pullback_firstOrder_unit_division p hp u (H i) (Sum.inr i) (hH i))
  rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp, map_sub, map_mul] at h
  exact h

end LinearStudy
