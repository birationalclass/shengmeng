module
public import Linear.PolynomialLocalCutRegular
public import Linear.ProjectivePulledSectionSmoothPoints
public import Linear.ProjectiveSmoothCommonDimension
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
namespace LinearStudy
open RingTheory.Sequence
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- At every smooth point of the ACTUAL finite reduced cut, its original
pulled equations form a regular sequence in the original local quotient.
The ambient normal generators are constructed from smoothness, and their
number is identified with n-r from the actual chart dimension. -/
theorem projectivePulledLinearSection_regular_at_smooth_affine_cut_point
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
    let P := RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom
    letI : P.IsPrime := RingHom.ker_isPrime _
    let A := Localization.AtPrime P
    let J := V.affineIdeal.map (algebraMap _ A)
    IsRegular (A ⧸ J) (List.ofFn (fun i : Fin r =>
      Ideal.Quotient.mk J (algebraMap _ A (affineChartPolynomialMap
        (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))))) := by
  let xs : Unit → Fin n → ℂ := fun _ => x
  let hxs : ∀ a, normalizedProjectivePoint (xs a) ∈ V.zeroSet := fun _ => hxV
  letI : ∀ a, Algebra.IsSmoothAt ℂ (V.affinePoint (xs a) (hxs a)).asIdeal := fun _ => hs
  obtain ⟨s,c,hdims,_,_,hc,e,M,hM,G,hH,hJ,hlocal,_⟩ :=
    projective_smooth_points_common_coordinates_actual_dimension V hproper xs hxs
  have hsr : s=r := by
    exact_mod_cast hdims.symm.trans hdim
  have hcr : c+r=n := by
    have hcard := Fintype.card_congr e
    simp only [Fintype.card_sum,Fintype.card_fin] at hcard
    omega
  let H : Fin r → MvPolynomial (Fin n) ℂ := fun i => affineChartPolynomialMap
    (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))
  have hI : (projectivePulledLinearSectionIdeal f V L w).map
      (affineChartPolynomialMap (K := ℂ)).toRingHom = V.affineIdeal ⊔ Ideal.span (Set.range H) :=
    projectivePulledLinearSectionIdeal_map_affine f V L w
  let C := MvPolynomial (Fin n) ℂ ⧸ (V.affineIdeal ⊔ Ideal.span (Set.range H))
  letI : _root_.IsReduced C :=
    isReduced_of_injective (Ideal.quotientEquivAlgOfEq ℂ hI).symm.toRingHom
      (Ideal.quotientEquivAlgOfEq ℂ hI).symm.injective
  letI : Module.Finite ℂ C := by dsimp [C];rw [← hI];infer_instance
  letI : IsArtinianRing C := IsArtinianRing.of_finite ℂ C
  have hpoint : V.affineIdeal ⊔ Ideal.span (Set.range H) ≤
      RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom := by
    intro F hF
    exact hx F (hI.symm ▸ hF)
  have hP := V.affinePointIdeal_comap x hxV
  change ((V.affinePoint x hxV).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)) =
    RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom at hP
  have hnormal := hlocal ()
  change V.affineIdeal.map (algebraMap _ (Localization.AtPrime
    ((V.affinePoint x hxV).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)))) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
        ((V.affinePoint x hxV).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal))) (G () i))) at hnormal
  let Q : PrimeSpectrum (MvPolynomial (Fin n) ℂ) :=
    ⟨(V.affinePoint x hxV).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal),inferInstance⟩
  let P : PrimeSpectrum (MvPolynomial (Fin n) ℂ) :=
    ⟨RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom,RingHom.ker_isPrime _⟩
  have he : Q=P := PrimeSpectrum.ext hP
  let E : PrimeSpectrum (MvPolynomial (Fin n) ℂ) → Prop := fun z =>
    V.affineIdeal.map (algebraMap _ (Localization.AtPrime z.asIdeal)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime z.asIdeal) (G () i)))
  have hQ : E Q := hnormal
  have hnormal' : E P := Eq.mp (congrArg E he) hQ
  exact polynomial_local_cut_equations_regular x V.affineIdeal (G ()) H hcr hnormal' hpoint

end LinearStudy
