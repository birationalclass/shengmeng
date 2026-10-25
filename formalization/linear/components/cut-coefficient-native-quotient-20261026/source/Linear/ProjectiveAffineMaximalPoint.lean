module
public import Linear.ProjectiveAffineSmoothLocus
public import Mathlib.RingTheory.Nullstellensatz
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace LinearStudy
/-- Every maximal ideal of the SAME original affine coordinate ring is
an actual complex point of V,with equality of the actual ideals. -/
theorem IntegralProjectiveEquations.affineMaximal_point
    {n : ℕ} (V : IntegralProjectiveEquations n)
    (p : Ideal (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) [p.IsMaximal] :
    ∃ (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet),
      (V.affinePoint x hx).asIdeal=p := by
  let pi := Ideal.Quotient.mk V.affineIdeal
  have hm : (p.comap pi).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective pi Ideal.Quotient.mk_surjective
  obtain ⟨x,hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hm
  have hk : p.comap pi=RingHom.ker (MvPolynomial.aeval (R:=ℂ) x).toRingHom := by
    rw [hx]
    ext a
    exact MvPolynomial.mem_vanishingIdeal_singleton_iff x a
  have hI : V.affineIdeal ≤ RingHom.ker (MvPolynomial.aeval (R:=ℂ) x).toRingHom := by
    rw [← hk]
    intro a ha
    change pi a ∈ p
    rw [show pi a=0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact p.zero_mem
  have hxV : normalizedProjectivePoint x ∈ V.zeroSet := by
    apply (V.normalizedPoint_mem_iff x).mpr
    have h := Ideal.map_le_iff_le_comap.mp hI
    rw [affineChartPolynomialMap_pointKernel_comap] at h
    exact h
  refine ⟨x,hxV,?_⟩
  apply Ideal.comap_injective_of_surjective pi Ideal.Quotient.mk_surjective
  exact (V.affinePointIdeal_comap x hxV).trans hk.symm
end LinearStudy
