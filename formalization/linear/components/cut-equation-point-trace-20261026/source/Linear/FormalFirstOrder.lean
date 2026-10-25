module
public import Linear.SmoothFormalQuotient
public import Linear.LocalFiberJacobian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ τ : Type*} [Field K] [Fintype σ] [DecidableEq σ] [Nonempty σ]

theorem powerSeries_maximalIdeal_eq_constantCoeff_kernel :
    IsLocalRing.maximalIdeal (MvPowerSeries σ K) =
      RingHom.ker (MvPowerSeries.constantCoeff (σ := σ) (R := K)) := by
  rw [← powerSeries_coordinateIdeal_eq_maximalIdeal, ← powerSeries_constantCoeff_kernel]

theorem powerSeries_firstOrder_derivative_constantCoeff
    (G v : MvPowerSeries σ K) (j : σ)
    (h : G - v ∈ (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) ^ 2) :
    (MvPowerSeries.pderiv j G).constantCoeff = (MvPowerSeries.pderiv j v).constantCoeff := by
  have hd := derivation_ideal_square (MvPowerSeries.pderiv j)
    (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) h
  rw [powerSeries_maximalIdeal_eq_constantCoeff_kernel] at hd
  change MvPowerSeries.constantCoeff (MvPowerSeries.pderiv j (G - v)) = 0 at hd
  rw [map_sub, map_sub] at hd
  exact sub_eq_zero.mp hd

theorem powerSeries_firstOrder_constantCoeff
    (G v : MvPowerSeries σ K)
    (h : G - v ∈ (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) ^ 2) :
    G.constantCoeff = v.constantCoeff := by
  have hm := Ideal.pow_le_self (I := IsLocalRing.maximalIdeal (MvPowerSeries σ K)) two_ne_zero h
  rw [powerSeries_maximalIdeal_eq_constantCoeff_kernel] at hm
  change MvPowerSeries.constantCoeff (G - v) = 0 at hm
  rw [map_sub] at hm
  exact sub_eq_zero.mp hm

theorem powerSeries_substitution_maps_square
    (v : σ → MvPowerSeries τ K) (hv : ∀ i, (v i).constantCoeff = 0)
    (F : MvPowerSeries σ K)
    (hF : F ∈ (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) ^ 2) :
    MvPowerSeries.substAlgHom (R := K) (MvPowerSeries.hasSubst_of_constantCoeff_zero hv) F ∈
      (Ideal.span (Set.range v)) ^ 2 := by
  let f := (MvPowerSeries.substAlgHom (R := K)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hv)).toRingHom
  have hm : (IsLocalRing.maximalIdeal (MvPowerSeries σ K)).map f =
      Ideal.span (Set.range v) := by
    rw [← powerSeries_coordinateIdeal_eq_maximalIdeal, Ideal.map_span, ← Set.range_comp]
    have he : (f ∘ MvPowerSeries.X) = v := by
      funext i
      exact MvPowerSeries.substAlgHom_X _ i
    rw [he]
  have hh := Ideal.mem_map_of_mem f hF
  rw [Ideal.map_pow, hm] at hh
  exact hh

theorem powerSeries_substitution_firstOrder
    (v : σ → MvPowerSeries τ K) (hv : ∀ i, (v i).constantCoeff = 0)
    (F : MvPowerSeries σ K) (j : σ)
    (hF : F - MvPowerSeries.X j ∈ (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) ^ 2) :
    MvPowerSeries.substAlgHom (R := K) (MvPowerSeries.hasSubst_of_constantCoeff_zero hv) F - v j ∈
      (Ideal.span (Set.range v)) ^ 2 := by
  have hh := powerSeries_substitution_maps_square v hv (F - MvPowerSeries.X j) hF
  rwa [map_sub, MvPowerSeries.substAlgHom_X] at hh

theorem normal_firstOrder_jacobian_identity
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty β]
    (G : β → MvPowerSeries (α ⊕ β) K)
    (hG : ∀ j, G j - MvPowerSeries.X (Sum.inr j) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (α ⊕ β) K)) ^ 2) :
    (fun i j => (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff) =
      (1 : Matrix β β K) := by
  ext i j
  rw [powerSeries_firstOrder_derivative_constantCoeff _ _ _ (hG i)]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply, Matrix.one_apply]

theorem normal_firstOrder_formal_coordinate_exists
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty β]
    (G : β → MvPowerSeries (α ⊕ β) K)
    (hG : ∀ j, G j - MvPowerSeries.X (Sum.inr j) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (α ⊕ β) K)) ^ 2) :
    ∃ E : MvPowerSeries (α ⊕ β) K ≃ₐ[K] MvPowerSeries (α ⊕ β) K,
      (∀ b : MvPowerSeries α K, E (MvPowerSeries.rename Sum.inl b) =
        MvPowerSeries.rename Sum.inl b) ∧
      ∀ j, E (MvPowerSeries.X (Sum.inr j)) = G j := by
  have h0 : ∀ j, (G j).constantCoeff = 0 := by
    intro j
    rw [powerSeries_firstOrder_constantCoeff _ _ (hG j)]
    simp
  have hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff)) := by
    rw [normal_firstOrder_jacobian_identity G hG, Matrix.det_one]
    exact isUnit_one
  exact ⟨smoothFormalCoordinateEquiv G h0 hJ,
    smoothFormalCoordinateEquiv_parameter_series G h0 hJ,
    smoothFormalCoordinateEquiv_normal G h0 hJ⟩

theorem span_unit_inv_scaled_family {R η : Type*} [CommRing R]
    (p : η → R) (u : Rˣ) :
    Ideal.span (Set.range (fun i => (u⁻¹ : Rˣ) * p i)) = Ideal.span (Set.range p) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ Ideal.mem_span_range_self
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h : (u⁻¹ : Rˣ) * p i ∈ Ideal.span (Set.range (fun i => (u⁻¹ : Rˣ) * p i)) :=
      Ideal.mem_span_range_self
    simpa [mul_assoc] using (Ideal.span (Set.range (fun i => (u⁻¹ : Rˣ) * p i))).mul_mem_left
      (u : R) h

theorem formal_pullback_firstOrder_unit_division
    (p : σ → MvPowerSeries τ K) (h0 : ∀ i, (p i).constantCoeff = 0)
    (u : (MvPowerSeries τ K)ˣ) (F : MvPowerSeries σ K) (j : σ)
    (hF : F - MvPowerSeries.X j ∈ (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) ^ 2) :
    let v := fun i => (u⁻¹ : (MvPowerSeries τ K)ˣ) * p i
    let hv : ∀ i, (v i).constantCoeff = 0 := by intro i; simp [v, h0 i]
    MvPowerSeries.substAlgHom (R := K) (MvPowerSeries.hasSubst_of_constantCoeff_zero hv) F -
      (u⁻¹ : (MvPowerSeries τ K)ˣ) * p j ∈ (Ideal.span (Set.range p)) ^ 2 := by
  let v := fun i => (u⁻¹ : (MvPowerSeries τ K)ˣ) * p i
  have hv : ∀ i, (v i).constantCoeff = 0 := by intro i; simp [v, h0 i]
  have hh := powerSeries_substitution_firstOrder v hv F j hF
  rwa [span_unit_inv_scaled_family p u] at hh

theorem formal_pullback_jacobian_unit_factor
    {β : Type*} [Fintype β] [DecidableEq β]
    (p : σ → MvPowerSeries τ K) (h0 : ∀ i, (p i).constantCoeff = 0)
    (u : (MvPowerSeries τ K)ˣ) (G : β → MvPowerSeries σ K)
    (targetNormal : β → σ) (sourceNormal : β → τ)
    (hG : ∀ i, G i - MvPowerSeries.X (targetNormal i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) ^ 2) :
    let I := Ideal.span (Set.range p)
    let v := fun i => (u⁻¹ : (MvPowerSeries τ K)ˣ) * p i
    let hv : ∀ i, (v i).constantCoeff = 0 := by intro i; simp [v, h0 i]
    let H := fun i => MvPowerSeries.substAlgHom (R := K)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hv) (G i)
    Ideal.Quotient.mk I (Matrix.det (fun i j => MvPowerSeries.pderiv (sourceNormal j) (H i))) =
      (Ideal.Quotient.mk I (u⁻¹ : (MvPowerSeries τ K)ˣ)) ^ Fintype.card β *
        Ideal.Quotient.mk I (Matrix.det (fun i j =>
          MvPowerSeries.pderiv (sourceNormal j) (p (targetNormal i)))) := by
  let I := Ideal.span (Set.range p)
  let v := fun i => (u⁻¹ : (MvPowerSeries τ K)ˣ) * p i
  have hv : ∀ i, (v i).constantCoeff = 0 := by intro i; simp [v, h0 i]
  let H := fun i => MvPowerSeries.substAlgHom (R := K)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hv) (G i)
  exact fiber_jacobian_unit_factor
    (fun j => MvPowerSeries.pderiv (sourceNormal j)) I u H (fun i => p (targetNormal i))
    (fun i => Ideal.mem_span_range_self)
    (fun i => formal_pullback_firstOrder_unit_division p h0 u (G i) (targetNormal i) (hG i))

end LinearStudy
