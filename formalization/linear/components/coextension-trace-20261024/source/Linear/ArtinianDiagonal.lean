module
public import Linear.PowerSeriesDiagonal
public import Linear.PowerSeriesAugmentation
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Actual diagonal Jacobian for an Artinian equation quotient

Derive nilpotence of each coordinate from Artinianity and the actual
augmentation. For a surjective power-series algebra map with nilpotent
coordinates, prove that coordinate differences generate the actual
kernel of tensor multiplication. Apply the difference-matrix construction
to the equation quotient: its determinant annihilates this kernel and
maps to the actual derivative Jacobian. No regularity, characteristic-zero,
Jacobian nonvanishing or trace identity is assumed or claimed here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
open scoped TensorProduct
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}

theorem powerSeriesQuotient_variable_nilpotent
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    (i : Fin (n + 1)) :
    IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.X i)) := by
  apply mem_nilradical.mp
  rw [← powerSeriesQuotientAugmentation_kernel_nilradical H hzero]
  change powerSeriesQuotientAugmentation H hzero
    (Ideal.Quotient.mk _ (MvPowerSeries.X i)) = 0
  simp

theorem powerSeries_tensor_diagonal_eq_coordinate_ideal
    {K : Type*} [CommRing K]
    {A ι : Type*} [CommRing A] [Algebra K A]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (q : MvPowerSeries ι K →ₐ[K] A) (hq : Function.Surjective q)
    (hnil : ∀ i, IsNilpotent (q (MvPowerSeries.X i))) :
    Ideal.span (Set.range (fun i =>
      q (MvPowerSeries.X i) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] q (MvPowerSeries.X i))) =
      KaehlerDifferential.ideal K A := by
  classical
  let l : A →ₐ[K] A ⊗[K] A := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[K] A ⊗[K] A := Algebra.TensorProduct.includeRight
  let u := l.toRingHom.comp q.toRingHom
  let v := r.toRingHom.comp q.toRingHom
  let π := (Algebra.TensorProduct.lmul' K : A ⊗[K] A →ₐ[K] A).toRingHom
  let D : Ideal (A ⊗[K] A) := Ideal.span (Set.range (fun i =>
    q (MvPowerSeries.X i) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] q (MvPowerSeries.X i)))
  have hc : ∀ c, u (MvPowerSeries.C c) = v (MvPowerSeries.C c) := by
    intro c
    change l (q (MvPowerSeries.C c)) = r (q (MvPowerSeries.C c))
    have hqc : q (MvPowerSeries.C c) = algebraMap K A c := by
      simpa [MvPowerSeries.algebraMap_apply] using q.commutes c
    rw [hqc, l.commutes, r.commutes]
  have hx : ∀ i, π (u (MvPowerSeries.X i)) = π (v (MvPowerSeries.X i)) := by
    intro i; simp [π, u, v, l, r]
  have hu : ∀ i, IsNilpotent (u (MvPowerSeries.X i)) := fun i => (hnil i).map l.toRingHom
  have hv : ∀ i, IsNilpotent (v (MvPowerSeries.X i)) := fun i => (hnil i).map r.toRingHom
  have hall : ∀ a : A, l a - r a ∈ D := by
    intro a
    obtain ⟨H, rfl⟩ := hq a
    obtain ⟨b, hb, hdb⟩ := powerSeries_diagonal_difference
      (R := K) (A := A ⊗[K] A) (B := A) (ι := ι) u v π hc hx hu hv H
    change u H - v H ∈ D
    rw [hb]
    apply Submodule.sum_mem
    intro i hi
    exact Ideal.mul_mem_left D _ (Ideal.subset_span (Set.mem_range_self i))
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp [KaehlerDifferential.ideal, RingHom.mem_ker]
  · rw [← KaehlerDifferential.span_range_eq_ideal]
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change (1 : A) ⊗ₜ[K] a - a ⊗ₜ[K] (1 : A) ∈ D
    simpa only [l, r, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, neg_sub] using D.neg_mem (hall a)

theorem powerSeriesQuotient_diagonal_jacobian
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))] :
    let Q := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)
    let q := Ideal.Quotient.mk (Ideal.span (Set.range H))
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Q ⊗[K] Q),
      Annihilates (KaehlerDifferential.ideal K Q) M.det ∧
      Algebra.TensorProduct.lmul' K M.det =
        Matrix.det (fun i j => q (MvPowerSeries.pderiv j (H i))) := by
  classical
  let Q := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)
  let q := Ideal.Quotient.mkₐ K (Ideal.span (Set.range H))
  let l : Q →ₐ[K] Q ⊗[K] Q := Algebra.TensorProduct.includeLeft
  let r : Q →ₐ[K] Q ⊗[K] Q := Algebra.TensorProduct.includeRight
  let u := l.toRingHom.comp q.toRingHom
  let v := r.toRingHom.comp q.toRingHom
  let π := (Algebra.TensorProduct.lmul' K : Q ⊗[K] Q →ₐ[K] Q).toRingHom
  have hc : ∀ c, u (MvPowerSeries.C c) = v (MvPowerSeries.C c) := by
    intro c
    change l (q (MvPowerSeries.C c)) = r (q (MvPowerSeries.C c))
    have hq : q (MvPowerSeries.C c) = algebraMap K Q c := by
      simpa [MvPowerSeries.algebraMap_apply] using q.commutes c
    rw [hq, l.commutes, r.commutes]
  have hx : ∀ i, π (u (MvPowerSeries.X i)) = π (v (MvPowerSeries.X i)) := by
    intro i; simp [π, u, v, l, r]
  have hu : ∀ i, IsNilpotent (u (MvPowerSeries.X i)) := by
    intro i; exact (powerSeriesQuotient_variable_nilpotent H hzero i).map l.toRingHom
  have hv : ∀ i, IsNilpotent (v (MvPowerSeries.X i)) := by
    intro i; exact (powerSeriesQuotient_variable_nilpotent H hzero i).map r.toRingHom
  have hH : ∀ i, u (H i) = v (H i) := by
    intro i
    have hz : q (H i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))
    change l (q (H i)) = r (q (H i))
    rw [hz, map_zero, map_zero]
  obtain ⟨M, hM, he, hd⟩ := powerSeries_diagonal_jacobian_matrix
    (R := K) (A := Q ⊗[K] Q) (B := Q) (ι := Fin (n + 1)) u v π hc hx hu hv H hH
  have hideal := powerSeries_tensor_diagonal_eq_coordinate_ideal q
    Ideal.Quotient.mk_surjective (fun i => powerSeriesQuotient_variable_nilpotent H hzero i)
  refine ⟨M, ?_, ?_⟩
  · rw [← hideal]
    exact hM
  change π M.det = Matrix.det (fun i j => q (MvPowerSeries.pderiv j (H i)))
  simpa [π, u, l] using hd

end LinearStudy
