module
public import Linear.ProjectiveVarietyLocalCutRegular
public import Linear.FiniteReducedRegularPointLocalData
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}
/-- On the SAME original finite reduced pulled cut,derive LOCAL CM and
actual point-local dimension from the already PROVED original smooth-point
regular sequence. Neither local CM nor local dimension is an input.
No global CM/S2/free canonical module or generic-open restriction. -/
theorem projectivePulledLinearSection_smooth_cut_point_local_data
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hproper : V.ideal.toIdeal ≠ ⊥)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)=(r : WithBot ℕ∞))
    (x : Fin n → ℂ) (hxV : normalizedProjectivePoint x ∈ V.zeroSet)
    (hs : Algebra.IsSmoothAt ℂ (V.affinePoint x hxV).asIdeal)
    (hx : x ∈ MvPolynomial.zeroLocus ℂ
      ((projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K := ℂ)).toRingHom))
    [_root_.IsReduced (MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K := ℂ)).toRingHom)]
    [Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K := ℂ)).toRingHom)] :
    let p := (V.affinePoint x hxV).asIdeal
    IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
      (r : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p) := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let H : Fin r → MvPolynomial (Fin n) ℂ := fun i => affineChartPolynomialMap
    (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))
  let rs := List.ofFn H
  let J := Ideal.ofList rs
  let pi := Ideal.Quotient.mk V.affineIdeal
  let ts := rs.map pi
  let p := (V.affinePoint x hxV).asIdeal
  have hspan : J=Ideal.span (Set.range H) := by
    simp [J,rs,Ideal.ofList,List.mem_ofFn,Set.range]
  have hI : (projectivePulledLinearSectionIdeal f V L w).map
      (affineChartPolynomialMap (K:=ℂ)).toRingHom=V.affineIdeal ⊔ J := by
    rw [hspan]
    exact projectivePulledLinearSectionIdeal_map_affine f V L w
  let C := MvPolynomial (Fin n) ℂ ⧸ (V.affineIdeal ⊔ J)
  let E := Ideal.quotientEquivAlgOfEq ℂ hI
  letI : IsReduced C := isReduced_of_injective E.symm.toRingHom E.symm.injective
  letI : Module.Finite ℂ C := by
    dsimp only [C]
    rw [← hI]
    infer_instance
  letI : IsArtinianRing C := IsArtinianRing.of_finite ℂ C
  let F := DoubleQuot.quotQuotEquivQuotSup V.affineIdeal J
  have hts : Ideal.ofList ts=J.map pi := by
    exact (Ideal.map_ofList pi rs).symm
  letI : IsReduced (B ⧸ Ideal.ofList ts) := by
    rw [hts]
    exact isReduced_of_injective F.toRingHom F.injective
  letI : IsArtinianRing (B ⧸ Ideal.ofList ts) := by
    rw [hts]
    exact F.symm.isArtinianRing
  have hp : Ideal.ofList ts ≤ p := by
    rw [hts]
    apply Ideal.map_le_iff_le_comap.mpr
    change J ≤ ((V.affinePoint x hxV).asIdeal).comap (Ideal.Quotient.mk V.affineIdeal)
    have he := V.affinePointIdeal_comap x hxV
    change ((V.affinePoint x hxV).asIdeal).comap (Ideal.Quotient.mk V.affineIdeal)=
      RingHom.ker (MvPolynomial.aeval (R:=ℂ) x).toRingHom at he
    rw [he]
    intro a ha
    exact hx a (hI.symm ▸ (show a ∈ V.affineIdeal ⊔ J from Ideal.mem_sup_right ha))
  have hreg := projectivePulledLinearSection_regular_in_variety_localRing
    f V hproper L w hdim x hxV hs hx
  have hreg' : RingTheory.Sequence.IsRegular (Localization.AtPrime p)
      (ts.map (algebraMap B (Localization.AtPrime p))) := by
    simpa only [ts,rs,H,pi,B,p,List.map_ofFn,Function.comp_def] using hreg
  have result := finite_reduced_regular_cut_point_local_data ts p hp hreg'
  exact ⟨result.1,by simpa only [ts,rs,List.length_map,List.length_ofFn,Fintype.card_fin] using result.2⟩
end LinearStudy
