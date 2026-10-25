module
public import Linear.ProjectiveCutEquationMapFinite
public import Linear.ProjectiveAffineMaximalPoint
public import Linear.ProjectiveSmoothCutPointLocalData
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
/-- EVERY maximal point over zero under the ACTUAL original equation map
is the SAME original cut point. The actual prime ideal is identified. -/
theorem projectivePulledCutEquation_zeroFiber_original_point {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (p : Ideal (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) [p.IsMaximal]
    (hp : p.comap (projectivePulledCutEquationMap f V L w).toRingHom=
      RingHom.ker (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom) :
    ∃ (x : Fin n → ℂ) (hxV : normalizedProjectivePoint x ∈ V.zeroSet),
      (V.affinePoint x hxV).asIdeal=p ∧
      x ∈ MvPolynomial.zeroLocus ℂ
        ((projectivePulledLinearSectionIdeal f V L w).map
          (affineChartPolynomialMap (K:=ℂ)).toRingHom) := by
  obtain ⟨x,hxV,hpx⟩ := V.affineMaximal_point p
  refine ⟨x,hxV,hpx,?_⟩
  have hk : p.comap (Ideal.Quotient.mk V.affineIdeal)=
      RingHom.ker (MvPolynomial.aeval (R:=ℂ) x).toRingHom := by
    subst p
    exact V.affinePointIdeal_comap x hxV
  apply (show (projectivePulledLinearSectionIdeal f V L w).map
      (affineChartPolynomialMap (K:=ℂ)).toRingHom ≤
      RingHom.ker (MvPolynomial.aeval (R:=ℂ) x).toRingHom from ?_)
  rw [projectivePulledLinearSectionIdeal_map_affine]
  apply sup_le (V.affineIdeal_le_pointKernel x hxV)
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  rw [← hk]
  have hi : MvPolynomial.X i ∈
      p.comap (projectivePulledCutEquationMap f V L w).toRingHom := by
    rw [hp]
    simp
  change projectivePulledCutEquationMap f V L w (MvPolynomial.X i) ∈ p at hi
  simpa only [projectivePulledCutEquationMap,AlgHom.comp_apply,MvPolynomial.aeval_X,Ideal.Quotient.mkₐ_eq_mk,SetLike.mem_coe,Ideal.mem_comap] using hi
/-- Original finite reduced cut and smoothness at its actual points DERIVE
local CM and dimension r at EVERY original maximal point above zero.
Neither CM,point dimension,nor a chosen independent point family is assumed. -/
theorem projectivePulledCutEquation_zeroFiber_all_point_local_data {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hproper : V.ideal.toIdeal ≠ ⊥)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)=(r : WithBot ℕ∞))
    (hsmooth : ∀ x : Fin n → ℂ,x ∈ MvPolynomial.zeroLocus ℂ
      ((projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K:=ℂ)).toRingHom) →
      ∃ hxV : normalizedProjectivePoint x ∈ V.zeroSet,
        Algebra.IsSmoothAt ℂ (V.affinePoint x hxV).asIdeal)
    [IsReduced (MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K:=ℂ)).toRingHom)]
    [Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K:=ℂ)).toRingHom)] :
    ∀ (p : Ideal (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) (_ : p.IsMaximal),
      p.comap (projectivePulledCutEquationMap f V L w).toRingHom=
        RingHom.ker (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom →
      IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
        (r : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p) := by
  intro p hp hzero
  letI : p.IsMaximal := hp
  obtain ⟨x,hxV,hpx,hx⟩ := projectivePulledCutEquation_zeroFiber_original_point f V L w p hzero
  obtain ⟨_,hs⟩ := hsmooth x hx
  subst p
  exact projectivePulledLinearSection_smooth_cut_point_local_data f V hproper L w hdim x hxV hs hx
end LinearStudy
