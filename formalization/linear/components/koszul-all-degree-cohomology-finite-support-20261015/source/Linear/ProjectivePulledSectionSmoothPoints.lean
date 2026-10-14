module
public import Linear.ProjectivePulledSectionGlobalReduced
public import Linear.ProjectiveWholeFiberPointLoci
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory
variable {n r : ℕ}

/-- An actual affine point of the original cut maps to the same original
linear section. No independent point family or evaluation ideal is used. -/
theorem projectivePulledLinearSection_affinePoint_image_mem
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (x : Fin n → ℂ)
    (hx : x ∈ MvPolynomial.zeroLocus ℂ
      ((projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K := ℂ)).toRingHom)) :
    normalizedProjectivePoint x ∈ V.zeroSet ∧
      f.onPoints (normalizedProjectivePoint x) ∈ projectiveLinearSection V L w := by
  let v : CoordinateVector n := Fin.cases 1 x
  have hvne : v ≠ 0 := normalizedCoordinateVector_ne_zero x
  have hv : v ∈ MvPolynomial.zeroLocus ℂ (projectivePulledLinearSectionIdeal f V L w) := by
    intro H hH
    have hz := hx _ (Ideal.mem_map_of_mem (affineChartPolynomialMap (K := ℂ)).toRingHom hH)
    exact (AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) x) H).symm.trans hz
  have hvI : v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal :=
    fun H hH => hv H (Ideal.mem_sup_left hH)
  have hxV : normalizedProjectivePoint x ∈ V.zeroSet := (V.normalizedPoint_mem_iff x).mpr hvI
  have hvH (i : Fin r) :
      MvPolynomial.eval v (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))=0 :=
    hv _ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i)))
  obtain ⟨u,hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hvne
  have hxH (i : Fin r) :
      MvPolynomial.eval (normalizedProjectivePoint x).rep
        (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))=0 := by
    change MvPolynomial.eval (Projectivization.mk ℂ v hvne).rep _=0
    rw [← hu,Units.smul_def,homogeneous_eval_smul
      (projective_pulled_back_section_forms_homogeneous f L hL w i),hvH i,mul_zero]
  refine ⟨hxV,?_⟩
  have he := projective_pulled_back_section_common_points f V hV L hL w
  have hm : normalizedProjectivePoint x ∈ {z : ProjectivePoint n | z ∈ V.zeroSet ∧ ∀ i,
    MvPolynomial.eval z.rep (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))=0} :=
    ⟨hxV,hxH⟩
  rw [he] at hm
  exact hm

/-- A constructed common good open retains the original finite reduced
native cut and proves EVERY actual affine cut point smooth on original V.
V itself is not assumed smooth or Cohen--Macaulay. -/
theorem projectivePulledLinearSection_exists_smooth_finite_reduced_cuts
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        let I := (projectivePulledLinearSectionIdeal f V L w).map
          (affineChartPolynomialMap (K := ℂ)).toRingHom
        let C := MvPolynomial (Fin n) ℂ ⧸ I
        w 0 ≠ 0 ∧ _root_.IsReduced C ∧ Module.Finite ℂ C ∧
          Nonempty (projectivePulledLinearSectionScheme f V L hL w ≅ Spec (CommRingCat.of C)) ∧
          AlgebraicGeometry.IsReduced (projectivePulledLinearSectionScheme f V L hL w) ∧
          (∀ x : Fin n → ℂ,x ∈ MvPolynomial.zeroLocus ℂ I →
            ∃ hx : normalizedProjectivePoint x ∈ V.zeroSet,
              Algebra.IsSmoothAt ℂ (V.affinePoint x hx).asIdeal) := by
  obtain ⟨a,ha,_,hcuts⟩ := projectivePulledLinearSection_exists_global_finite_reduced_schemes
    f V hq hf hV L hL hinj hfinite x0 hx0
  obtain ⟨p,hp,hgood,_,_⟩ := projective_exists_general_whole_reduced_fibers
    f V hq hf hV x0 hx0
  obtain ⟨D,H,hHom,hH,hchart⟩ := projective_exists_homogeneous_chart_avoidance V x0 hx0 p hp
  obtain ⟨b,hb,havoid⟩ := finite_linear_projection_exists_projective_section_avoiding
    V L hL hfinite H hHom hH
  have hc : a*b ≠ 0 := mul_ne_zero ha hb
  have hex : ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w (a*b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (MvPolynomial.funext (fun w => by simpa using h w))
  refine ⟨a*b,hc,hex,?_⟩
  intro w hw
  obtain ⟨hwa,hwb⟩ := mul_ne_zero_iff.mp (by simpa only [MvPolynomial.eval_mul] using hw)
  obtain ⟨hw0,hred,hfin,hiso,hsch⟩ := hcuts w hwa
  refine ⟨hw0,hred,hfin,hiso,hsch,?_⟩
  intro x hx
  obtain ⟨hxV,hsect⟩ := projectivePulledLinearSection_affinePoint_image_mem f V hV L hL w x hx
  let z := f.onPoints (normalizedProjectivePoint x)
  obtain ⟨hz0,hyp⟩ := hchart z.rep (havoid w hw0 hwb z hsect)
  let y : Fin n → ℂ := fun i => z.rep i.succ/z.rep 0
  have hy : normalizedProjectivePoint y ∈ V.zeroSet :=
    V.normalizedConePoint_mem z.rep hsect.1 hz0
  have hzy : normalizedProjectivePoint y=z :=
    (normalizedProjectivePoint_coordinate_ratios z.rep (Projectivization.rep_nonzero z) hz0).trans
      (Projectivization.mk_rep z)
  obtain ⟨_,hsmooth,_,_,_⟩ := projective_whole_fiber_point_actual_good_loci
    f V hq hf hV x0 hx0 p hgood y x hy hxV hyp hzy.symm
  exact ⟨hxV,hsmooth⟩

end LinearStudy
