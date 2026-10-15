module
public import Linear.ProjectiveAffineLinearSection
public import Linear.LinearProjectionSectionAvoidance
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- Actual affine-section functions embed in the original cone-section
quotient by normalizing its X0 coordinate. A left inverse is constructed
by normalizing L0. This comparison preserves nilpotents. -/
theorem projectiveAffineLinearSection_exists_injective_cone_map
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (w : Fin (r+1) → ℂ) (hw0 : w 0 ≠ 0)
    (hX : IsUnit (Ideal.Quotient.mk (polynomialProjectionFiberIdeal V.ideal.toIdeal L w)
      (MvPolynomial.X 0))) :
    ∃ α : (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w) →ₐ[ℂ]
      (CoordinateRing n ⧸ polynomialProjectionFiberIdeal V.ideal.toIdeal L w),
      Function.Injective α ∧
        ∀ i, α (Ideal.Quotient.mk (projectiveAffineLinearSectionIdeal V L w)
          (MvPolynomial.X i)) =
          (↑(hX.unit⁻¹) : CoordinateRing n ⧸ polynomialProjectionFiberIdeal V.ideal.toIdeal L w) *
            Ideal.Quotient.mk (polynomialProjectionFiberIdeal V.ideal.toIdeal L w)
              (MvPolynomial.X i.succ) := by
  let I := projectiveAffineLinearSectionIdeal V L w
  let J := polynomialProjectionFiberIdeal V.ideal.toIdeal L w
  let A := MvPolynomial (Fin n) ℂ ⧸ I
  let B := CoordinateRing n ⧸ J
  have hCA (c : ℂ) : Ideal.Quotient.mk I (MvPolynomial.C c)=algebraMap ℂ A c := by
    rw [← MvPolynomial.algebraMap_eq,Ideal.Quotient.mk_algebraMap]
  have hCB (c : ℂ) : Ideal.Quotient.mk J (MvPolynomial.C c)=algebraMap ℂ B c := by
    rw [← MvPolynomial.algebraMap_eq,Ideal.Quotient.mk_algebraMap]
  let a : Fin (n+1) → A := Fin.cases 1 (fun i => Ideal.Quotient.mk I (MvPolynomial.X i))
  let z : Fin (n+1) → B := fun i => Ideal.Quotient.mk J (MvPolynomial.X i)
  let v := hX.unit
  have hv : (v : B) = z 0 := hX.unit_spec
  let invz : B := ↑(v⁻¹)
  have hinvz : invz*z 0=1 := by simp [invz, ← hv]
  let hU := projectiveAffineLinearSection_L0_isUnit V L hL hfinite w hw0
  let u := hU.unit
  let l : Fin (r+1) → A := fun i => Ideal.Quotient.mk I (affineChartPolynomialMap (L i))
  have hu : (u : A)=l 0 := hU.unit_spec
  let b : A := algebraMap ℂ A (w 0) * ↑(u⁻¹)
  have hae : MvPolynomial.aeval a =
      (Ideal.Quotient.mkₐ ℂ I).comp affineChartPolynomialMap := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply]
    change a i=Ideal.Quotient.mk I (affineChartPolynomialMap (MvPolynomial.X i))
    rw [affineChartPolynomialMap, MvPolynomial.aeval_X]
    cases i using Fin.cases <;> simp [a]
  have hvI : ∀ P ∈ V.ideal.toIdeal, MvPolynomial.aeval a P=0 := by
    intro P hP
    rw [hae, AlgHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left
      (Ideal.mem_map_of_mem affineChartPolynomialMap.toRingHom hP))
  let β₀ : CoordinateRing n →ₐ[ℂ] A := MvPolynomial.aeval (fun i => b*a i)
  have hβI : ∀ P ∈ V.ideal.toIdeal, β₀ P=0 :=
    homogeneousIdeal_aeval_scaled_zero _ V.ideal.isHomogeneous a hvI b
  have hrel (i : Fin r) : algebraMap ℂ A (w 0)*l i.succ =
      algebraMap ℂ A (w i.succ)*l 0 := by
    have he : Ideal.Quotient.mk I
        (affineChartPolynomialMap (projectiveLinearSectionForms L w i))=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right
        (Ideal.subset_span (Set.mem_range_self i)))
    simpa [projectiveLinearSectionForms,linearSectionSourceForms,l,
      sub_eq_zero, hCA] using he
  have hbL (i : Fin (r+1)) : b*l i=algebraMap ℂ A (w i) := by
    cases i using Fin.cases with
    | zero => simp [b, ← hu, mul_assoc]
    | succ i =>
      calc
        b*l i.succ = (↑(u⁻¹) : A)*(algebraMap ℂ A (w 0)*l i.succ) := by dsimp [b]; ring
        _ = (↑(u⁻¹) : A)*(algebraMap ℂ A (w i.succ)*l 0) := by rw [hrel]
        _ = _ := by simp [← hu, mul_comm, mul_assoc]
  have hβL (i : Fin (r+1)) : β₀ (L i)=algebraMap ℂ A (w i) := by
    change MvPolynomial.aeval (fun j => b*a j) (L i)=_
    rw [homogeneous_aeval_smul (hL i), pow_one, hae, AlgHom.comp_apply]
    exact hbL i
  have hβJ : ∀ P ∈ J, β₀ P=0 := by
    have hle : J ≤ RingHom.ker β₀.toRingHom := by
      apply sup_le
      · exact hβI
      · apply Ideal.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change β₀ (L i-MvPolynomial.C (w i))=0
        rw [map_sub, MvPolynomial.algHom_C, hβL, sub_self]
    exact fun P hP => hle hP
  let β : B →ₐ[ℂ] A := Ideal.Quotient.liftₐ J β₀ hβJ
  have hzI : ∀ P ∈ V.ideal.toIdeal, MvPolynomial.aeval z P=0 := by
    have hz : MvPolynomial.aeval z=Ideal.Quotient.mkₐ ℂ J := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X]
      rfl
    intro P hP
    rw [hz]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hP)
  let α₀ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] B :=
    MvPolynomial.aeval (fun i => invz*z i.succ)
  have hαe : α₀.comp affineChartPolynomialMap=
      MvPolynomial.aeval (fun i => invz*z i) := by
    rw [affineChartPolynomialMap_comp_aeval]
    congr 1
    funext i
    cases i using Fin.cases with
    | zero => exact hinvz.symm
    | succ i => rfl
  have hαI : ∀ P ∈ V.affineIdeal, α₀ P=0 := by
    have hle : V.affineIdeal ≤ RingHom.ker α₀.toRingHom := by
      unfold IntegralProjectiveEquations.affineIdeal
      rw [Ideal.map_le_iff_le_comap]
      intro P hP
      change α₀ (affineChartPolynomialMap P)=0
      rw [← AlgHom.comp_apply, hαe]
      exact homogeneousIdeal_aeval_scaled_zero _ V.ideal.isHomogeneous z hzI invz P hP
    exact fun P hP => hle hP
  have hzL (i : Fin (r+1)) : Ideal.Quotient.mk J (L i)=algebraMap ℂ B (w i) := by
    have he : Ideal.Quotient.mk J (L i-MvPolynomial.C (w i))=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right
        (Ideal.subset_span (Set.mem_range_self i)))
    simpa [map_sub, sub_eq_zero, hCB] using he
  have hαH (i : Fin r) :
      α₀ (affineChartPolynomialMap (projectiveLinearSectionForms L w i))=0 := by
    rw [← AlgHom.comp_apply,hαe,
      homogeneous_aeval_smul (projectiveLinearSectionForms_homogeneous L hL w i),pow_one]
    have hz : MvPolynomial.aeval z=Ideal.Quotient.mkₐ ℂ J := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [MvPolynomial.aeval_X]
      rfl
    rw [hz, Ideal.Quotient.mkₐ_eq_mk]
    have he : Ideal.Quotient.mk J (projectiveLinearSectionForms L w i)=0 := by
      simp [projectiveLinearSectionForms,linearSectionSourceForms,hzL,hCB]
      ring
    rw [he,mul_zero]
  have hαJ : ∀ P ∈ I, α₀ P=0 := by
    have hle : I ≤ RingHom.ker α₀.toRingHom := by
      apply sup_le
      · exact hαI
      · apply Ideal.span_le.mpr
        rintro _ ⟨i,rfl⟩
        exact hαH i
    exact fun P hP => hle hP
  let α : A →ₐ[ℂ] B := Ideal.Quotient.liftₐ I α₀ hαJ
  have hαmk (P : MvPolynomial (Fin n) ℂ) : α (Ideal.Quotient.mk I P)=α₀ P := by
    dsimp only [α]
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl
  have hβz (i : Fin (n+1)) : β (z i)=b*a i := by
    dsimp only [β,z]
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact MvPolynomial.aeval_X ..
  have hβinv : β invz*b=1 := by
    have he := congrArg β hinvz
    rw [map_mul,map_one,hβz] at he
    simpa [a] using he
  have hβαmk : (β.comp α).comp (Ideal.Quotient.mkₐ ℂ I)=Ideal.Quotient.mkₐ ℂ I := by
    apply MvPolynomial.algHom_ext
    intro i
    change β (α (Ideal.Quotient.mk I (MvPolynomial.X i)))=
      Ideal.Quotient.mk I (MvPolynomial.X i)
    rw [hαmk]
    rw [show α₀ (MvPolynomial.X i)=invz*z i.succ from MvPolynomial.aeval_X ..]
    rw [map_mul,hβz,← mul_assoc,hβinv,one_mul]
    rfl
  have hβα : β.comp α=AlgHom.id ℂ A := by
    apply AlgHom.ext
    intro t
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective t
    exact AlgHom.congr_fun hβαmk P
  refine ⟨α, ?_, ?_⟩
  · exact Function.LeftInverse.injective (fun t => AlgHom.congr_fun hβα t)
  · intro i
    rw [hαmk]
    exact MvPolynomial.aeval_X ..

/-- The actual affine section quotient is reduced and finite whenever
the cone equation fiber is so and lies in X0≠0. The inference uses the
explicit normalized ring map, not a point-set bijection. -/
theorem projectiveAffineLinearSection_radical_finite_of_cone
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (w : Fin (r+1) → ℂ) (hw0 : w 0 ≠ 0)
    (hX : IsUnit (Ideal.Quotient.mk (polynomialProjectionFiberIdeal V.ideal.toIdeal L w)
      (MvPolynomial.X 0)))
    (hrad : (polynomialProjectionFiberIdeal V.ideal.toIdeal L w).IsRadical)
    (hfin : Module.Finite ℂ
      (CoordinateRing n ⧸ polynomialProjectionFiberIdeal V.ideal.toIdeal L w)) :
    (projectiveAffineLinearSectionIdeal V L w).IsRadical ∧
      Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w) := by
  let J := polynomialProjectionFiberIdeal V.ideal.toIdeal L w
  let I := projectiveAffineLinearSectionIdeal V L w
  letI : IsReduced (CoordinateRing n ⧸ J) :=
    (Ideal.isRadical_iff_quotient_reduced J).mp hrad
  letI := hfin
  obtain ⟨α,hα,_⟩ := projectiveAffineLinearSection_exists_injective_cone_map
    V L hL hfinite w hw0 hX
  letI : IsReduced (MvPolynomial (Fin n) ℂ ⧸ I) :=
    isReduced_of_injective α.toRingHom hα
  exact ⟨(Ideal.isRadical_iff_quotient_reduced I).mpr inferInstance,
    Module.Finite.of_injective α.toLinearMap hα⟩

/-- From the SAME actual linear normalization and original nonempty
chart, construct a nonempty target open on which the affine linear-section
equation ideal is radical and its quotient is finite. -/
theorem projective_linear_normalization_exists_affine_radical_sections
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
        w 0 ≠ 0 ∧ (projectiveAffineLinearSectionIdeal V L w).IsRadical ∧
          Module.Finite ℂ
            (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w) := by
  letI := V.prime
  obtain ⟨a,ha,hfib⟩ := polynomial_finite_projection_exists_radical_equation_fibers
    V.ideal.toIdeal L hinj hfinite
  have hX : (MvPolynomial.X (0 : Fin (n+1)) : CoordinateRing n) ∉ V.ideal.toIdeal := by
    intro h
    have he := (V.normalizedPoint_mem_iff x0).mp hx0 _ h
    simpa using he
  obtain ⟨b,hb,havoid⟩ := finite_polynomial_projection_exists_cone_fiber_avoiding
    V.ideal.toIdeal L hfinite (MvPolynomial.X 0) hX
  let c : MvPolynomial (Fin (r+1)) ℂ := a*b*MvPolynomial.X 0
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) (MvPolynomial.X_ne_zero 0)
  have hex : ∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  have hp : (MvPolynomial.eval w a ≠ 0 ∧ MvPolynomial.eval w b ≠ 0) ∧ w 0 ≠ 0 :=
    by simpa only [c,map_mul,MvPolynomial.eval_X,mul_ne_zero_iff] using hw
  let J := polynomialProjectionFiberIdeal V.ideal.toIdeal L w
  have hu : IsUnit (Ideal.Quotient.mk J (MvPolynomial.X 0)) := by
    apply polynomialQuotient_isUnit_of_nonvanishing
    intro v hv
    have hvI : v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal :=
      fun P hP => hv P (Ideal.mem_sup_left hP)
    have hvL : (fun i => MvPolynomial.eval v (L i))=w := by
      funext i
      have hi := hv _ (Ideal.mem_sup_right
        (Ideal.subset_span (Set.mem_range_self i)))
      simpa [MvPolynomial.aeval_eq_eval,sub_eq_zero] using hi
    simpa using havoid w hp.1.2 v hvI hvL
  obtain ⟨hrad,hfin,_,_⟩ := hfib w hp.1.1
  exact ⟨hp.2,projectiveAffineLinearSection_radical_finite_of_cone V L hL hfinite w hp.2 hu hrad hfin⟩

end LinearStudy
