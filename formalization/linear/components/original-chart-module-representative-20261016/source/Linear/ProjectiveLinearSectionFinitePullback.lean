module
public import Linear.FiniteReducedClosedBaseChange
public import Linear.ProjectiveLinearSectionReducedPullbackOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- The EXACT extension of an actual target point ideal has the same
quotient algebra as the original finite fiber-equation quotient. -/
theorem projectiveAffineFiber_pointIdeal_map_quotient_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet) :
    Module.Finite ℂ
      (Localization.Away (projectiveChartDenominator f V) ⧸
        (RingHom.ker (V.affinePointEvaluation y hy).toRingHom).map
          (projectiveChartOpenMap f V hq hf hV y hy).toRingHom) := by
  letI := projectiveAffineFiberQuotient_finite f V hq y
  have hk := projectiveAffineFiberChartMap_ker_eq_pointIdeal_map f V hq hf hV y hy
  let e := (Ideal.quotientEquivAlgOfEq ℂ hk.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (projectiveAffineFiberChartMap_surjective f V y))
  exact Module.Finite.of_injective e.toLinearMap e.injective

/-- A finite reduced ORIGINAL target section has a finite original-f
pulled quotient. The actual fibers, their residue evaluations, and their
kernel/ideal equalities are constructed, rather than assumed as a product. -/
theorem projectiveChartLinearSection_map_quotient_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hrad : (projectiveAffineLinearSectionIdeal V L w).IsRadical)
    [Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w)] :
    Module.Finite ℂ
      (Localization.Away (projectiveChartDenominator f V) ⧸
        (projectiveChartLinearSectionIdeal V L w).map
          (projectiveChartOpenMap f V hq hf hV x0 hx0).toRingHom) := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let I := projectiveChartLinearSectionIdeal V L w
  let C := B ⧸ I
  let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
  obtain ⟨hred,hfinite⟩ := projectiveChartLinearSection_quotient_reduced_finite V L w hrad
  letI : _root_.IsReduced C := hred
  letI : Module.Finite ℂ C := hfinite
  letI : IsArtinianRing C := isArtinian_of_tower ℂ inferInstance
  obtain ⟨q,hqres⟩ := finiteAlgebra_exists_maximal_residue_evaluations (K := ℂ) (A := C)
  apply reducedArtinian_closed_baseChange_quotient_finite φ I
  intro p
  let π : B →ₐ[ℂ] C := Ideal.Quotient.mkₐ ℂ I
  let ρ := (q p).comp π
  obtain ⟨y,hy,_,heval⟩ := V.affineAlgHom_point_evaluation ρ
  have hρ : ρ=V.affinePointEvaluation y hy := by
    apply AlgHom.ext
    intro a
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [V.affinePointEvaluation_mk]
    exact AlgHom.congr_fun heval P
  have hkρ : RingHom.ker ρ.toRingHom=p.asIdeal.comap π.toRingHom := by
    change RingHom.ker ((q p).toRingHom.comp π.toRingHom)=_
    rw [← RingHom.comap_ker,hqres p]
  have hk : p.asIdeal.comap (Ideal.Quotient.mk I)=
      RingHom.ker (V.affinePointEvaluation y hy).toRingHom := by
    change p.asIdeal.comap π.toRingHom=_
    rw [← hkρ,hρ]
  rw [hk]
  exact projectiveAffineFiber_pointIdeal_map_quotient_finite f V hq hf hV y hy

/-- A constructed nonempty target open gives FINITE REDUCED actual
pulled equation algebras in the original denominator chart. Finiteness,
reducedness, and their common defining ideal are all proved from f,V and
the same original finite linear normalization. Global Proj gluing is open. -/
theorem projectiveLinearSection_exists_finite_reduced_pullbacks
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
        w 0 ≠ 0 ∧
          _root_.IsReduced (Localization.Away (projectiveChartDenominator f V) ⧸
            projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w)) ∧
          Module.Finite ℂ (Localization.Away (projectiveChartDenominator f V) ⧸
            projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w)) := by
  obtain ⟨c,hc,hex,hgood⟩ := projectiveLinearSection_exists_reduced_pullback_open
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hrad,hfin,hpull⟩ := hgood w hw
  letI := hfin
  have hid := projectiveChartLinearSection_map_eq_pulled_equationIdeal
    f V hq hf hV x0 hx0 L hL w
  have hfinitePull := projectiveChartLinearSection_map_quotient_finite
    f V hq hf hV x0 hx0 L w hrad
  exact ⟨hw0,(Ideal.isRadical_iff_quotient_reduced _).mp hpull,hid ▸ hfinitePull⟩

end LinearStudy
