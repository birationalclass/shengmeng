module
public import Linear.ProjectiveAffineFiberFinite
public import Linear.ProjectiveNormalizedConePoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {n : ℕ}

/-- Conversely, an actual normalized source point in the specified
projective fiber satisfies ALL the affine fiber-equation ideal. -/
theorem projectiveAffineFiberIdeal_mem_of_point
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y z : Fin n → ℂ)
    (hz : normalizedProjectivePoint z ∈ V.zeroSet)
    (hfy : f.onPoints (normalizedProjectivePoint z) = normalizedProjectivePoint y) :
    z ∈ MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) := by
  let v : CoordinateVector n := Fin.cases 1 z
  have hvec : Projectivization.mk ℂ (f.evalVector v) (f.noBasePoint v
      (normalizedCoordinateVector_ne_zero z)) =
      Projectivization.mk ℂ (Fin.cases 1 y) (normalizedCoordinateVector_ne_zero y) := hfy
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hvec
  have heval (i : Fin (n + 1)) :
      MvPolynomial.eval z (affineChartPolynomialMap (f.forms i)) = f.evalVector v i :=
    AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) z) (f.forms i)
  have h0 : (a : ℂ) = f.evalVector v 0 := by
    have h := congrFun ha 0
    change (a : ℂ) * 1 = f.evalVector v 0 at h
    simpa using h
  have hrel (i : Fin n) : MvPolynomial.aeval z
      (affineChartPolynomialMap (f.forms i.succ) -
        MvPolynomial.C (y i) * affineChartPolynomialMap (f.forms 0)) = 0 := by
    have hi : (a : ℂ) * y i = f.evalVector v i.succ := congrFun ha i.succ
    simp only [map_sub, map_mul, MvPolynomial.aeval_C]
    change MvPolynomial.eval z (affineChartPolynomialMap (f.forms i.succ)) -
      y i * MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0)) = 0
    rw [heval, heval, ← h0, ← hi, mul_comm, sub_self]
  have hle : projectiveAffineFiberIdeal f V y ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
    apply sup_le (V.affineIdeal_le_pointKernel z hz)
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact hrel i
  intro p hp
  exact hle hp

/-- If the ENTIRE projective fiber avoids the source hyperplane, the
actual affine fiber zeroes are in bijection with that ENTIRE point fiber. -/
theorem projectiveAffineFiber_nonempty_whole_point_equiv
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (hchart : ∀ (v : CoordinateVector n) (hv : v ≠ 0),
      f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) :
    Nonempty (MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) ≃
      (f.onPoints ⁻¹' {normalizedProjectivePoint y})) := by
  let j : MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) →
      (f.onPoints ⁻¹' {normalizedProjectivePoint y}) := fun z =>
    ⟨normalizedProjectivePoint z.1, (projectiveAffineFiberIdeal_point f V y z.1 z.2).2.2⟩
  have hinj : Function.Injective j := by
    intro z z' h
    exact Subtype.ext (normalizedProjectivePoint_injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective j := by
    intro p
    let v := p.1.rep
    have hv : v ≠ 0 := Projectivization.rep_nonzero p.1
    have hfv : f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y := by
      rw [Projectivization.mk_rep]
      exact p.2
    have hv0 := hchart v hv hfv
    let z : Fin n → ℂ := fun i => v i.succ / v 0
    have hnorm := normalizedProjectivePoint_coordinate_ratios v hv hv0
    have hfz : f.onPoints (normalizedProjectivePoint z) = normalizedProjectivePoint y := by
      rw [hnorm]
      exact hfv
    have hz : normalizedProjectivePoint z ∈ V.zeroSet := by
      rw [← hV]
      change f.onPoints (normalizedProjectivePoint z) ∈ V.zeroSet
      rwa [hfz]
    refine ⟨⟨z, projectiveAffineFiberIdeal_mem_of_point f V y z hz hfz⟩, ?_⟩
    apply Subtype.ext
    exact hnorm.trans (Projectivization.mk_rep p.1)
  exact ⟨Equiv.ofBijective j ⟨hinj, hsurj⟩⟩

end LinearStudy
