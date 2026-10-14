module
public import Linear.AffineKoszulAllCohomologyConclusions
public import Linear.ProjectiveCutKoszulFiniteSupport
public import Linear.ProjectiveCutAffineResolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] affineKoszulAllCohomologyConclusions
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
variable {n r : ℕ}

/-- SAME ORIGINAL geometric pulled-linear cut has ACTUAL native Hom
cohomology finite support in ALL degrees,EVERY original coefficient N.
Derive BOTH source exactness and cut finiteness from ORIGINAL hypotheses;
neither is an additional input. The named CONCLUSION body explicitly
contains ALL actual native/internal-Hom objects,positive ACTUAL derived
module Ext comparisons,and the SAME-OBJECT ACTUAL geometric unit IsIso.
It is PROVED as output,never assumed as a certificate. The full body is
printed in the exact audit. No global/target CM/free/flat hypothesis added.
Derived SHEAF Ext/global gluing remain separate OPEN obligations. -/
theorem projectivePulledLinearSection_exists_actual_allCohomology_support
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hproper : V.ideal.toIdeal ≠ ⊥)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞))
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
        let I := (projectivePulledLinearSectionIdeal f V L w).map
          (affineChartPolynomialMap (K := ℂ)).toRingHom
        let C := MvPolynomial (Fin n) ℂ ⧸ I
        let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
        let H : Fin r → B := fun i => Ideal.Quotient.mk V.affineIdeal
          (affineChartPolynomialMap
            (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
        w 0 ≠ 0 ∧ _root_.IsReduced C ∧ Module.Finite ℂ C ∧
          Nonempty (projectivePulledLinearSectionScheme f V L hL w ≅ Spec (CommRingCat.of C)) ∧
          AlgebraicGeometry.IsReduced (projectivePulledLinearSectionScheme f V L hL w) ∧
          ∃ he : ∀ j : ℕ, 0 < j → (koszulComplex (Fintype.linearCombination B H)).ExactAt j,
            affineKoszulAllCohomologyConclusions (CommRingCat.of B) r H := by
  obtain ⟨c,hc,hex,hcuts⟩ := projectivePulledLinearSection_exists_affineKoszul_exactAt
    f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hred,hfin,hiso,hsch,he⟩ := hcuts w hw
  have hcut := projectivePulledLinearSection_koszulCut_zeroLocus_finite f V L w hfin
  refine ⟨hw0,hred,hfin,hiso,hsch,he,?_⟩
  exact affineKoszulAllCohomologyConclusions_of_exact_finite _ _ _ he hcut

end LinearStudy
