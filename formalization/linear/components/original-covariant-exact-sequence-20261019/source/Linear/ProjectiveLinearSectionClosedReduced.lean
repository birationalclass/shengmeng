module
public import Linear.ReducedClosedBaseChange
public import Linear.ProjectiveAffineFiberClosedPullback
public import Linear.ProjectiveAffineLinearSectionComparison
public import Linear.NativeProjectiveChartClosedPullback
public import Linear.AffineRationalPointValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- The original linear-section defining ideal in the original affine
coordinate ring of V, before its pullback by the original map. -/
def projectiveChartLinearSectionIdeal
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (w : Fin (r+1) → ℂ) : Ideal (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) :=
  (Ideal.span (Set.range (fun i =>
    affineChartPolynomialMap (projectiveLinearSectionForms L w i)))).map
      (Ideal.Quotient.mk V.affineIdeal)

/-- The actual double quotient is reduced and finite by its ORIGINAL
affine-section algebra equivalence, not by an assumed point decomposition. -/
theorem projectiveChartLinearSection_quotient_reduced_finite
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (w : Fin (r+1) → ℂ)
    (hrad : (projectiveAffineLinearSectionIdeal V L w).IsRadical)
    [Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w)] :
    IsReduced ((MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ⧸ projectiveChartLinearSectionIdeal V L w) ∧
      Module.Finite ℂ ((MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ⧸
        projectiveChartLinearSectionIdeal V L w) := by
  let K : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span (Set.range (fun i =>
    affineChartPolynomialMap (projectiveLinearSectionForms L w i)))
  let e := DoubleQuot.quotQuotEquivQuotSupₐ ℂ V.affineIdeal K
  letI : IsReduced (MvPolynomial (Fin n) ℂ ⧸ (V.affineIdeal ⊔ K)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hrad
  letI : Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ (V.affineIdeal ⊔ K)) :=
    (inferInstance : Module.Finite ℂ
      (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w))
  exact ⟨isReduced_of_injective e.toRingHom e.injective,
    Module.Finite.of_injective e.toLinearMap e.injective⟩

/-- Actual reduced fibers at ALL points of a finite reduced target section
give radicality of its exact original-f extended ideal. All residue points
are constructed and identified with original normalized points of V. -/
theorem projectiveChartLinearSection_map_isRadical_of_reduced_fibers
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hrad : (projectiveAffineLinearSectionIdeal V L w).IsRadical)
    [Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w)]
    (hfib : ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
      (∀ i, MvPolynomial.eval y (affineChartPolynomialMap (projectiveLinearSectionForms L w i))=0) →
        IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y)) :
    ((projectiveChartLinearSectionIdeal V L w).map
      (projectiveChartOpenMap f V hq hf hV x0 hx0).toRingHom).IsRadical := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let I := projectiveChartLinearSectionIdeal V L w
  let C := B ⧸ I
  let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
  obtain ⟨hred,hfinite⟩ := projectiveChartLinearSection_quotient_reduced_finite V L w hrad
  letI : IsReduced C := hred
  letI : Module.Finite ℂ C := hfinite
  letI : IsArtinianRing C := isArtinian_of_tower ℂ inferInstance
  obtain ⟨q,hqres⟩ := finiteAlgebra_exists_maximal_residue_evaluations (K := ℂ) (A := C)
  apply reducedArtinian_closed_baseChange_ideal_isRadical φ.toRingHom I
  intro p
  let π : B →ₐ[ℂ] C := Ideal.Quotient.mkₐ ℂ I
  let ρ := (q p).comp π
  obtain ⟨y,hy,_,heval⟩ := V.affineAlgHom_point_evaluation ρ
  have hρ : ρ = V.affinePointEvaluation y hy := by
    apply AlgHom.ext
    intro a
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [V.affinePointEvaluation_mk]
    exact AlgHom.congr_fun heval P
  have hvan (i : Fin r) :
      MvPolynomial.eval y (affineChartPolynomialMap (projectiveLinearSectionForms L w i))=0 := by
    let H := affineChartPolynomialMap (projectiveLinearSectionForms L w i)
    have hm : Ideal.Quotient.mk V.affineIdeal H ∈ I :=
      Ideal.mem_map_of_mem (Ideal.Quotient.mk V.affineIdeal)
        (Ideal.subset_span (Set.mem_range_self i))
    have hz : π (Ideal.Quotient.mk V.affineIdeal H)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    have hzρ : ρ (Ideal.Quotient.mk V.affineIdeal H)=0 := by
      change q p (π (Ideal.Quotient.mk V.affineIdeal H))=0
      rw [hz,map_zero]
    exact (AlgHom.congr_fun heval H).symm.trans hzρ
  letI := hfib y hy hvan
  have hkρ : RingHom.ker ρ.toRingHom = p.asIdeal.comap π.toRingHom := by
    change RingHom.ker ((q p).toRingHom.comp π.toRingHom)=_
    rw [← RingHom.comap_ker,hqres p]
  have hk : p.asIdeal.comap (Ideal.Quotient.mk I) =
      RingHom.ker (V.affinePointEvaluation y hy).toRingHom := by
    change p.asIdeal.comap π.toRingHom = _
    rw [← hkρ,hρ]
  rw [hk]
  exact projectiveAffineFiber_pointIdeal_map_isRadical f V hq hf hV y hy

/-- Exact equality between the original chart ideal extension and the
actual substituted homogeneous-equation ideal used by the native pullback. -/
theorem projectiveChartLinearSection_map_eq_pulled_equationIdeal
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) :
    (projectiveChartLinearSectionIdeal V L w).map
      (projectiveChartOpenMap f V hq hf hV x0 hx0).toRingHom =
        projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let H := projectiveLinearSectionForms L w
  let hH := projectiveLinearSectionForms_homogeneous L hL w
  let I := projectiveChartLinearSectionIdeal V L w
  let e := projectiveNativeChartRingEquiv V x0 hx0
  let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
  let ψ := projectiveNativeChartPullback f V hq hf hV x0 hx0
  let J := projectiveNativeChartEquationIdeal V (fun _ : Fin r => 1) H hH
  have he : I.map e.toRingHom=J := by
    change (Ideal.span (Set.range (fun i => affineChartPolynomialMap (H i))) |>
      Ideal.map (Ideal.Quotient.mk V.affineIdeal)).map e.toRingHom=J
    rw [Ideal.map_map,Ideal.map_span,← Set.range_comp']
    have hgen (i : Fin r) :
        e (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (H i))) =
          projectiveNativeChartHomogeneousElement V 1 (H i) (hH i) :=
      projectiveNativeChartRingEquiv_homogeneous_mk V x0 hx0 1 (H i) (hH i)
    change Ideal.span (Set.range (fun i : Fin r =>
      e (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (H i)))))=J
    simp only [hgen]
    rfl
  have hcomp : ψ.comp e.toRingHom=φ.toRingHom := by
    apply RingHom.ext
    intro a
    change φ (e.symm (e a))=φ a
    rw [RingEquiv.symm_apply_apply]
  calc
    I.map φ.toRingHom=(I.map e.toRingHom).map ψ := by rw [Ideal.map_map,hcomp]
    _ = projectiveNativeChartPullbackEquationIdeal f V H := by
      rw [he]
      exact projectiveNativeChartEquationIdeal_map f V hq hf hV x0 hx0 (fun _ => 1) H hH

end LinearStudy
