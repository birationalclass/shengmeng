module
public import Linear.ProjectiveAffineFiberUniversal
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
variable {n : ℕ}

/-- The SAME original chart pullback extends the target point ideal to the
EXACT kernel of the actual polynomial fiber quotient. No radical replacement
is made: the universal property proves equality including nilpotents. -/
theorem projectiveAffineFiberChartMap_ker_eq_pointIdeal_map
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet) :
    RingHom.ker (projectiveAffineFiberChartMap f V y).toRingHom =
      (RingHom.ker (V.affinePointEvaluation y hy).toRingHom).map
        (projectiveChartOpenMap f V hq hf hV y hy).toRingHom := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV y hy
  let ρ := V.affinePointEvaluation y hy
  let q := projectiveAffineFiberChartMap f V y
  let J := (RingHom.ker ρ.toRingHom).map φ.toRingHom
  have hle : J ≤ RingHom.ker q.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change q (φ b) = 0
    have h := AlgHom.congr_fun (projectiveAffineFiberChartMap_pullback f V hq hf hV y hy) b
    change q (φ b) = algebraMap ℂ _ (ρ b) at h
    change ρ b = 0 at hb
    rw [h, hb, map_zero]
  let C := A ⧸ J
  let χ : A →ₐ[ℂ] C := Ideal.Quotient.mkₐ ℂ J
  have hχ : χ.comp φ = (Algebra.ofId ℂ C).comp ρ := by
    apply AlgHom.ext
    intro b
    have hb : b - algebraMap ℂ B (ρ b) ∈ RingHom.ker ρ.toRingHom := by
      change ρ (b - algebraMap ℂ B (ρ b)) = 0
      rw [map_sub, ρ.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have hm : φ (b - algebraMap ℂ B (ρ b)) ∈ J :=
      Ideal.mem_map_of_mem φ.toRingHom hb
    have hz : χ (φ (b - algebraMap ℂ B (ρ b))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [map_sub, map_sub, φ.commutes, χ.commutes, sub_eq_zero] at hz
    change χ (φ b) = algebraMap ℂ C (ρ b)
    exact hz
  obtain ⟨ψ,hψ,_⟩ := projectiveAffineFiberChartMap_exists_unique_lift
    f V hq hf hV y hy χ hχ
  apply le_antisymm _ hle
  intro a ha
  change q a = 0 at ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change χ a = 0
  have h := AlgHom.congr_fun hψ a
  change ψ (q a) = χ a at h
  rw [← h, ha, map_zero]

/-- An original reduced fiber quotient makes its actual extended point
ideal radical. Reducedness is an input here for one fiber; it is derived
on the simultaneous good open by the separate original-f construction. -/
theorem projectiveAffineFiber_pointIdeal_map_isRadical
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    [IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y)] :
    ((RingHom.ker (V.affinePointEvaluation y hy).toRingHom).map
      (projectiveChartOpenMap f V hq hf hV y hy).toRingHom).IsRadical := by
  rw [← projectiveAffineFiberChartMap_ker_eq_pointIdeal_map f V hq hf hV y hy]
  exact (RingHom.ker_isRadical_iff_reduced_of_surjective
    (projectiveAffineFiberChartMap_surjective f V y)).mpr inferInstance

end LinearStudy
