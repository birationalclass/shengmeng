module
public import Linear.AffineKoszulOriginalSheafExtClass
public import Linear.ProjectiveCutAffineKoszul
public import Linear.ChosenProjectiveNormalizationDimensions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
/-- Source exactness and the SAME original SHEAF Ext/class law for EVERY
coefficient module at ONCE. Statement only. The exactness witness is fixed
BEFORE N and its actual injective resolution I;no comparison certificate. -/
def affineKoszulOriginalSheafExtAllCoefficientsClassStatement
    (R : CommRingCat.{u}) (p : ℕ) (H : Fin (p+1) → R) : Prop :=
  ∃ he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j,
    ∀ (N : ModuleCat.{u} R) (I : InjectiveResolution (tilde N)),
      schemeModuleOriginalTopExtClassIsoLaw (tildeFunctionKoszulComplex R H) (p+1)
        (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
          (tildeKoszulOriginalCutCokernelCofork R H))
        (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he)
        (affineKoszulOriginalSheafExtGeometricIso R N p H he I)
        (affineKoszulHomGeometricRestrictionPresentation R N p H).g
/-- The constructed actual class square works uniformly for arbitrary N.
Original source exactness is the sole input;all Ext acyclicity is derived. -/
theorem affineKoszulOriginalSheafExtAllCoefficientsClassStatement_of_exact
    (R : CommRingCat.{u}) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j) :
    affineKoszulOriginalSheafExtAllCoefficientsClassStatement R p H :=
  ⟨he,fun N I => affineKoszulOriginalSheafExtGeometricIso_classLaw R N p H he I⟩
/-- SAME original pulled cut equations over the actual original affine
coordinate ring,not freely chosen equations. Statement only;fixed C_L,
global twists and SAME original top-H trace are not asserted. -/
def projectivePulledCutEquationActualSheafExtClassStatement {n p : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin ((p+1)+1) → CoordinateRing n) (w : Fin ((p+1)+1) → ℂ) : Prop :=
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let H : Fin (p+1) → B := fun i => Ideal.Quotient.mk V.affineIdeal
    (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
  affineKoszulOriginalSheafExtAllCoefficientsClassStatement (CommRingCat.of B) p H
/-- FULL ORIGINAL Setup DERIVES one nonempty original parameter open on
which actual SHEAF Ext and SAME original class/geometric restriction law
hold for EVERY original coefficient module N. No source exactness, Ext
vanishing, coefficient freeness or desired comparison is added to Setup. -/
theorem projectivePulledCutEquation_originalSetup_exists_actualSheafExtClass_open {n p : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : p+1 < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin ((p+1)+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin ((p+1)+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin ((p+1)+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin ((p+1)+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        projectivePulledCutEquationActualSheafExtClassStatement f V L w := by
  obtain ⟨c,hc,hex,hcuts⟩ := projectivePulledLinearSection_exists_affineKoszul_exactAt f V
    (chosenProjectiveNormalization_definingIdeal_ne_bot V L hinj hfinite hrn)
    hq hf hV L hL hinj hfinite
    (chosenProjectiveNormalization_chart_dimension V L hinj hfinite x0 hx0) x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨_,_,_,_,_,he⟩ := hcuts w hw
  exact affineKoszulOriginalSheafExtAllCoefficientsClassStatement_of_exact _ p _ he
end LinearStudy
