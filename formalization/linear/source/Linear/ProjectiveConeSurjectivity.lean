module
public import Linear.ProjectiveIdealInvariance
public import Mathlib.FieldTheory.IsAlgClosed.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Positive-degree projective surjectivity gives actual surjectivity of
the homogeneous map on vectors, using roots in the complex field. -/
theorem HomogeneousEndomorphism.evalVector_surjective
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree)
    (hf : Function.Surjective f.onPoints) : Function.Surjective f.evalVector := by
  intro w
  by_cases hw : w = 0
  · subst w
    exact ⟨0, f.evalVector_zero (Nat.ne_of_gt hq)⟩
  obtain ⟨z, hz⟩ := hf (Projectivization.mk ℂ w hw)
  induction z using Projectivization.ind with
  | h v hv =>
    rw [f.onPoints_mk] at hz
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hz.symm
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) hq
    refine ⟨b • v, ?_⟩
    rw [f.evalVector_smul, hb]
    exact ha

theorem projective_surjective_invariant_cone_image
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    f.evalVector '' MvPolynomial.zeroLocus ℂ V.ideal.toIdeal =
      MvPolynomial.zeroLocus ℂ V.ideal.toIdeal := by
  have hp := projective_total_invariance_cone f V (Nat.ne_of_gt hq) hV
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change v ∈ f.evalVector ⁻¹' MvPolynomial.zeroLocus ℂ V.ideal.toIdeal
    rwa [hp]
  · intro hw
    obtain ⟨v, hv⟩ := f.evalVector_surjective hq hf w
    refine ⟨v, ?_, hv⟩
    rw [← hp]
    change f.evalVector v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal
    rwa [hv]

/-- The induced endomorphism on the actual homogeneous coordinate domain
has zero kernel; ideal contraction follows from actual cone surjectivity. -/
theorem projective_surjective_invariant_pullback_comap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    V.ideal.toIdeal.comap (MvPolynomial.aeval f.forms).toRingHom = V.ideal.toIdeal := by
  ext H
  constructor
  · intro hH
    have hvan : H ∈ MvPolynomial.vanishingIdeal ℂ
        (MvPolynomial.zeroLocus ℂ V.ideal.toIdeal) := by
      intro w hw
      rw [← projective_surjective_invariant_cone_image f V hq hf hV] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      have he := hv ((MvPolynomial.aeval f.forms) H) hH
      change MvPolynomial.eval v (MvPolynomial.eval₂ MvPolynomial.C f.forms H) = 0 at he
      exact (MvPolynomial.eval_assoc f.forms v H).trans he
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, V.prime.radical] at hvan
    exact hvan
  · intro hH
    exact (projective_total_invariance_ideal_power_sandwich f V (Nat.ne_of_gt hq) hV).choose_spec.2.2
      (Ideal.mem_map_of_mem _ hH)

end LinearStudy
