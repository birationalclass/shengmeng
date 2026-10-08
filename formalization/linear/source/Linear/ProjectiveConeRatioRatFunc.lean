module
public import Linear.ProjectiveConeCoordinateTranscendental
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The actual cone field is generated over the actual projective
ratio field by its single nonzero scaling coordinate. -/
theorem projectiveConeRatioField_adjoin_coordinate_top
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    IntermediateField.adjoin (projectiveCoordinateRatioField V)
      {projectiveConeFractionCoordinates V 0} = ⊤ := by
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  let E := projectiveCoordinateRatioField V
  let K := IntermediateField.adjoin E {projectiveConeFractionCoordinates V 0}
  let L := K.restrictScalars ℂ
  have ht : projectiveConeFractionCoordinates V 0 ∈ K :=
    IntermediateField.subset_adjoin E _ (Set.mem_singleton _)
  have hz := projectiveConeFractionCoordinates_zero_ne_zero V x hx
  have hc : ∀ i, projectiveConeFractionCoordinates V i ∈ L := by
    intro i
    induction i using Fin.cases with
    | zero => exact ht
    | succ j =>
      have hr : projectiveConeFractionCoordinates V j.succ /
          projectiveConeFractionCoordinates V 0 ∈ E :=
        IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩
      have hrK : projectiveConeFractionCoordinates V j.succ /
          projectiveConeFractionCoordinates V 0 ∈ K :=
        K.algebraMap_mem ⟨_, hr⟩
      rw [← div_mul_cancel₀ (projectiveConeFractionCoordinates V j.succ) hz]
      exact K.mul_mem hrK ht
  have hp : ∀ P : CoordinateRing n,
      MvPolynomial.aeval (projectiveConeFractionCoordinates V) P ∈ L := by
    intro P
    exact MvPolynomial.eval₂_mem (fun _ _ => L.algebraMap_mem _) hc
  have ha : ∀ a : A, algebraMap A F a ∈ L := by
    intro a
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← projectiveConeFractionCoordinates_aeval]
    exact hp P
  have hL : L = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective A z
    rw [← hab]
    exact L.div_mem (ha a) (ha b)
  apply IntermediateField.restrictScalars_injective ℂ
  exact hL

/-- An explicit rational-function-field model of the ORIGINAL cone field;
the coefficient field is the ORIGINAL projective coordinate-ratio field. -/
def projectiveConeRatioRatFuncEquiv
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    RatFunc (projectiveCoordinateRatioField V) ≃ₐ[projectiveCoordinateRatioField V]
      FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal) := by
  letI := V.prime
  exact (RatFunc.algEquivOfTranscendental (projectiveConeFractionCoordinates V 0)
    (projectiveConeFractionCoordinates_zero_transcendental V x hx)).trans
      ((IntermediateField.equivOfEq (projectiveConeRatioField_adjoin_coordinate_top V x hx)).trans
        IntermediateField.topEquiv)

theorem projectiveConeRatioRatFuncEquiv_X
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    projectiveConeRatioRatFuncEquiv V x hx (RatFunc.X : RatFunc (projectiveCoordinateRatioField V)) =
      projectiveConeFractionCoordinates V 0 := by
  letI := V.prime
  simp [projectiveConeRatioRatFuncEquiv]

end LinearStudy
