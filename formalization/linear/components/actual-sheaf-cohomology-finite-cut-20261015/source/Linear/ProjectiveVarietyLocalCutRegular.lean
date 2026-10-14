module
public import Linear.ProjectiveSmoothCutRegular
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
namespace LinearStudy
open RingTheory.Sequence
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- The regular sequence consists of the SAME original cut equations in
the actual local ring of the original affine variety at the actual point. -/
theorem projectivePulledLinearSection_regular_in_variety_localRing
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
    IsRegular (Localization.AtPrime p) (List.ofFn (fun i : Fin r =>
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) (Localization.AtPrime p)
        (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap
          (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))))) := by
  intro p
  let H : Fin r → MvPolynomial (Fin n) ℂ := fun i => affineChartPolynomialMap
    (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))
  let Q : PrimeSpectrum (MvPolynomial (Fin n) ℂ) :=
    ⟨p.comap (Ideal.Quotient.mk V.affineIdeal),inferInstance⟩
  let P : PrimeSpectrum (MvPolynomial (Fin n) ℂ) :=
    ⟨RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom,RingHom.ker_isPrime _⟩
  have hQP : Q=P := PrimeSpectrum.ext (V.affinePointIdeal_comap x hxV)
  let E : PrimeSpectrum (MvPolynomial (Fin n) ℂ) → Prop := fun z =>
    let A := Localization.AtPrime z.asIdeal
    let J := V.affineIdeal.map (algebraMap _ A)
    IsRegular (A ⧸ J) (List.ofFn (fun i => Ideal.Quotient.mk J (algebraMap _ A (H i))))
  have hP : E P := projectivePulledLinearSection_regular_at_smooth_affine_cut_point
    f V hproper L w hdim x hxV hs hx
  have hQ : E Q := Eq.mpr (congrArg E hQP) hP
  let A := Localization.AtPrime Q.asIdeal
  let J := V.affineIdeal.map (algebraMap _ A)
  let e := localizationQuotientEquiv V.affineIdeal p
  let rs := List.ofFn (fun i => Ideal.Quotient.mk J (algebraMap _ A (H i)))
  have hmul : List.Forall₂ (fun (a : A ⧸ J) (b : Localization.AtPrime p) =>
      ∀ z, e (a • z)=b • e z) rs (rs.map e) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun a _ z => e.map_mul a z))
  change IsRegular (A ⧸ J) rs at hQ
  have hreg : IsRegular (Localization.AtPrime p) (rs.map e) :=
    (AddEquiv.isRegular_congr (e := e.toRingEquiv.toAddEquiv)
      (R := A ⧸ J) (S := Localization.AtPrime p) hmul).mp hQ
  have hlist : rs.map e=List.ofFn (fun i =>
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) (Localization.AtPrime p)
        (Ideal.Quotient.mk V.affineIdeal (H i))) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact localizationQuotientEquiv_mk V.affineIdeal p (H i)
  rw [hlist] at hreg
  exact hreg

/-- The actual original cut's exterior-power Koszul complex is exact
in every positive degree at its actual smooth affine point. -/
theorem projectivePulledLinearSection_localKoszul_exactAt_smooth_cut_point
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
    let R := Localization.AtPrime p
    let H : Fin r → R := fun i => algebraMap (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) R
      (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap
        (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))
    ∀ j : ℕ,0 < j →
      (koszulComplex (R := R) (M := Fin r → R) (Fintype.linearCombination R H)).ExactAt j := by
  intro p R H j hj
  have hreg := projectivePulledLinearSection_regular_in_variety_localRing
    f V hproper L w hdim x hxV hs hx
  have he := koszulComplex.exactAt_of_isRegular (List.ofFn H) hreg j (Nat.ne_of_gt hj)
  rw [koszul_ofFn] at he
  exact he

end LinearStudy
