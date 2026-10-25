module
public import Linear.ArbitraryParameterSocle
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic

/-! Actual derivative and determinant calculations in a fiber quotient. First-order equation congruences and a unit denominator imply the precise determinant factor and transfer nonzero annihilator classes. The geometric smooth-chart and completed local-ring comparisons supplying these equations remain separate obligations. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace LinearStudy

theorem derivation_ideal_square {K R : Type*} [CommRing K] [CommRing R]
    [Algebra K R] (D : Derivation K R R) (I : Ideal R) {h : R}
    (hh : h ∈ I ^ 2) : D h ∈ I := by
  rw [pow_two] at hh
  refine Submodule.mul_induction_on hh ?_ ?_
  · intro a ha b hb
    rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    exact I.add_mem (I.mul_mem_right _ ha) (I.mul_mem_right _ hb)
  · intro a b ha hb
    rw [map_add]
    exact I.add_mem ha hb

theorem first_order_derivative_quotient {K R : Type*} [CommRing K] [CommRing R]
    [Algebra K R] (D : Derivation K R R) (I : Ideal R) {h v : R}
    (hh : h - v ∈ I ^ 2) :
    Ideal.Quotient.mk I (D h) = Ideal.Quotient.mk I (D v) := by
  have hd := derivation_ideal_square D I hh
  rw [map_sub] at hd
  exact (sub_eq_zero.mp (by
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hd))

theorem unit_divided_derivative_quotient {K R : Type*} [CommRing K] [CommRing R]
    [Algebra K R] (D : Derivation K R R) (I : Ideal R) (u : Rˣ) (p : R)
    (hp : p ∈ I) :
    Ideal.Quotient.mk I (D ((u⁻¹ : Rˣ) * p)) =
      Ideal.Quotient.mk I (u⁻¹ : Rˣ) * Ideal.Quotient.mk I (D p) := by
  rw [D.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
    Ideal.Quotient.eq_zero_iff_mem.mpr hp]
  simp

theorem fiber_jacobian_unit_factor {K R ι : Type*} [CommRing K] [CommRing R]
    [Algebra K R] [Fintype ι] [DecidableEq ι]
    (D : ι → Derivation K R R) (I : Ideal R) (u : Rˣ) (H p : ι → R)
    (hp : ∀ i, p i ∈ I) (hH : ∀ i, H i - (u⁻¹ : Rˣ) * p i ∈ I ^ 2) :
    Ideal.Quotient.mk I (Matrix.det (fun i j => D j (H i))) =
      (Ideal.Quotient.mk I (u⁻¹ : Rˣ)) ^ Fintype.card ι *
        Ideal.Quotient.mk I (Matrix.det (fun i j => D j (p i))) := by
  classical
  rw [RingHom.map_det, RingHom.map_det]
  change Matrix.det (fun i j => Ideal.Quotient.mk I (D j (H i))) =
    (Ideal.Quotient.mk I (u⁻¹ : Rˣ)) ^ Fintype.card ι *
      Matrix.det (fun i j => Ideal.Quotient.mk I (D j (p i)))
  have hm : (fun i j => Ideal.Quotient.mk I (D j (H i))) =
      Ideal.Quotient.mk I (u⁻¹ : Rˣ) •
        (fun i j => Ideal.Quotient.mk I (D j (p i))) := by
    funext i j
    rw [first_order_derivative_quotient (D j) I (hH i),
      unit_divided_derivative_quotient (D j) I u (p i) (hp i)]
    rfl
  rw [hm, Matrix.det_smul]

theorem fiber_jacobian_nonzero {K R ι : Type*} [CommRing K] [CommRing R]
    [Algebra K R] [Fintype ι] [DecidableEq ι]
    (D : ι → Derivation K R R) (I : Ideal R) (u : Rˣ) (H p : ι → R)
    (hp : ∀ i, p i ∈ I) (hH : ∀ i, H i - (u⁻¹ : Rˣ) * p i ∈ I ^ 2)
    (hne : Ideal.Quotient.mk I (Matrix.det (fun i j => D j (H i))) ≠ 0) :
    Ideal.Quotient.mk I (Matrix.det (fun i j => D j (p i))) ≠ 0 := by
  intro hz
  apply hne
  rw [fiber_jacobian_unit_factor D I u H p hp hH, hz, mul_zero]

theorem unit_mul_annihilates_iff {R : Type*} [CommRing R] (N : Ideal R)
    (u : Rˣ) (delta : R) : Annihilates N ((u : R) * delta) ↔ Annihilates N delta := by
  constructor
  · intro h n hn
    apply u.mul_right_eq_zero.mp
    calc (u : R) * (n * delta) = n * ((u : R) * delta) := by ring
         _ = 0 := h n hn
  · intro h n hn
    calc n * ((u : R) * delta) = (u : R) * (n * delta) := by ring
         _ = 0 := by rw [h n hn, mul_zero]

theorem fiber_jacobian_annihilates {K R ι : Type*} [CommRing K] [CommRing R]
    [Algebra K R] [Fintype ι] [DecidableEq ι]
    (D : ι → Derivation K R R) (I : Ideal R) (u : Rˣ) (H p : ι → R)
    (hp : ∀ i, p i ∈ I) (hH : ∀ i, H i - (u⁻¹ : Rˣ) * p i ∈ I ^ 2)
    (N : Ideal (R ⧸ I))
    (hd : Annihilates N (Ideal.Quotient.mk I (Matrix.det (fun i j => D j (H i))))) :
    Annihilates N (Ideal.Quotient.mk I (Matrix.det (fun i j => D j (p i)))) := by
  rw [fiber_jacobian_unit_factor D I u H p hp hH] at hd
  exact (unit_mul_annihilates_iff N
    ((Units.map (Ideal.Quotient.mk I).toMonoidHom u⁻¹) ^ Fintype.card ι) _).mp hd

end LinearStudy
