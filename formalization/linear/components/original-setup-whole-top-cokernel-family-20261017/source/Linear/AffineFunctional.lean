module
public import Linear.FilteredIdeal
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic
/-! A low-degree vanishing functional is constructed on the actual affine quotient from positive-degree regular highest parts with origin-only zero locus. Its normalization is on the highest-part Euler determinant. It is not yet identified with the normalized universal diagonal functional or geometric residue. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
variable {K ι : Type*} [Field K]

theorem affine_filtered_functional_descends {n : ℕ}
    (P : Fin n → MvPolynomial ι K)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial ι K)
      (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
    (D : ℕ)
    (hrep : ∀ p : MvPolynomial ι K, ∃ r : MvPolynomial ι K,
      r.totalDegree ≤ D ∧ Ideal.Quotient.mk (Ideal.span (Set.range P)) p =
        Ideal.Quotient.mk (Ideal.span (Set.range P)) r)
    (rho : (MvPolynomial ι K ⧸ Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) →ₗ[K] K) :
    ∃ ell : (MvPolynomial ι K ⧸ Ideal.span (Set.range P)) →ₗ[K] K,
      (∀ f : MvPolynomial ι K, f.totalDegree ≤ D →
        ell (Ideal.Quotient.mk (Ideal.span (Set.range P)) f) =
          rho (Ideal.Quotient.mk (Ideal.span (Set.range
            (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
              (MvPolynomial.homogeneousComponent D f))) ∧
      ∀ f : MvPolynomial ι K, f.totalDegree < D →
        ell (Ideal.Quotient.mk (Ideal.span (Set.range P)) f) = 0 := by
  classical
  let I := Ideal.span (Set.range P)
  let J := Ideal.span (Set.range (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))
  let W := MvPolynomial.restrictTotalDegree ι K D
  let pi := Ideal.Quotient.mkₐ K I
  let pj := Ideal.Quotient.mkₐ K J
  let f : W →ₗ[K] (MvPolynomial ι K ⧸ I) := pi.toLinearMap.comp W.subtype
  let g : W →ₗ[K] K := rho.comp (pj.toLinearMap.comp
    ((MvPolynomial.homogeneousComponent D).comp W.subtype))
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, hr, he⟩ := hrep p
    exact ⟨⟨r, (MvPolynomial.mem_restrictTotalDegree ι D r).mpr hr⟩, he.symm⟩
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hz : Ideal.Quotient.mk I (x : MvPolynomial ι K) = 0 := LinearMap.mem_ker.mp hx
    have hm : (x : MvPolynomial ι K) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hdeg : (x : MvPolynomial ι K).totalDegree ≤ D :=
      (MvPolynomial.mem_restrictTotalDegree ι D _).mp x.property
    have ht := affine_ideal_top_component_mem P hreg x hm D hdeg
    apply LinearMap.mem_ker.mpr
    change rho (Ideal.Quotient.mk J (MvPolynomial.homogeneousComponent D (x : MvPolynomial ι K))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ht, map_zero]
  let ell := f.liftOfSurjective hsurj ⟨g, hker⟩
  have he : ∀ p : MvPolynomial ι K, p.totalDegree ≤ D →
      ell (pi p) = rho (pj (MvPolynomial.homogeneousComponent D p)) := by
    intro p hp
    exact LinearMap.equivOfSurjective_apply (f := f) hsurj hker
      (m := ⟨p, (MvPolynomial.mem_restrictTotalDegree ι D p).mpr hp⟩)
  refine ⟨ell, he, ?_⟩
  intro p hp
  change ell (pi p) = 0
  rw [he p hp.le, MvPolynomial.homogeneousComponent_eq_zero D p hp, map_zero, map_zero]

theorem affine_polynomial_low_degree_functional [IsAlgClosed K] [CharZero K] {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (he : ∀ i, 0 < (P i).totalDegree)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) K)
      (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0}) :
    let I := Ideal.span (Set.range P)
    let H := fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)
    let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) K) :=
      fun i j => MvPolynomial.C (((P i).totalDegree : K)⁻¹) * MvPolynomial.pderiv j (H i)
    ∃ ell : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₗ[K] K,
      ell (Ideal.Quotient.mk I M.det) = 1 ∧
      ∀ f : MvPolynomial (Fin (n + 1)) K,
        f.totalDegree < ∑ i, ((P i).totalDegree - 1) → ell (Ideal.Quotient.mk I f) = 0 := by
  classical
  let H := fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)
  let e := fun i => (P i).totalDegree
  let D := ∑ i, (e i - 1)
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) K) :=
    fun i j => MvPolynomial.C ((e i : K)⁻¹) * MvPolynomial.pderiv j (H i)
  have hH : ∀ i, (H i).IsHomogeneous (e i) := fun i =>
    MvPolynomial.homogeneousComponent_isHomogeneous _ _
  obtain ⟨p, hn, _, _⟩ := homogeneous_polynomial_low_degree_pairing H e he hH hreg hz
  obtain ⟨ell, hell, hv⟩ := affine_filtered_functional_descends P hreg D
    (affine_polynomial_bounded_normal_form P he hreg hz) p.functional
  have hMhom : M.det.IsHomogeneous D := (homogeneous_euler_coefficient_matrix H e hH he).2
  refine ⟨ell, ?_, hv⟩
  rw [hell M.det hMhom.totalDegree_le, MvPolynomial.homogeneousComponent_eq_self hMhom]
  exact hn

end LinearStudy
