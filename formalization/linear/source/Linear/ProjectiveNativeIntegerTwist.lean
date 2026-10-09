module
public import Linear.NativeProjectiveIntegerTwistLocallyFree
public import Linear.Projective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The integer homogeneous twist on the ORIGINAL native projective
variety is locally free, using its actual coordinate chart cover. -/
theorem projectiveNativeIntegerTwist_isLocallyFree {n : ℕ}
    (V : IntegralProjectiveEquations n) (m : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) m).IsLocallyFree := by
  let := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  let a : Fin (n+1) → (CoordinateRing n ⧸ V.ideal.toIdeal) :=
    fun i => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i)
  have ha : ∀ i, a i ∈ 𝓑 1 :=
    fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i, rfl⟩
  let q := nativeIntegerTwistLocalGeneratorsData 𝓑 a ha m
    (homogeneousQuotient_native_coordinate_chart_cover V.ideal.toIdeal V.ideal.isHomogeneous)
  let : q.IsLocallyFreeData :=
    nativeIntegerTwistLocalGeneratorsData_isLocallyFreeData 𝓑 a ha m _
  exact q.isLocallyFree

/-- The ORIGINAL native integer twist is quasicoherent; no coherent
sheaf model, chart cover, or local trivialization is supplied. -/
theorem projectiveNativeIntegerTwist_isQuasicoherent {n : ℕ}
    (V : IntegralProjectiveEquations n) (m : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) m).IsQuasicoherent := by
  let := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let := projectiveNativeIntegerTwist_isLocallyFree V m
  infer_instance

end LinearStudy
