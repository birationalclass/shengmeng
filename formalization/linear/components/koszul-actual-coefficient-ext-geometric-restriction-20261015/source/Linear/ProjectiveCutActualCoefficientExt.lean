module
public import Linear.KoszulExactTopExtCoefficientRestriction
public import Linear.ProjectiveCutAffineResolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
variable {n r : ℕ}

/-- Apply ACTUAL arbitrary-coefficient derived MODULE Ext to the SAME
original pulled linear cut in positive dimension. The positive exactness
is DERIVED from the existing all-prime regular-or-unit cut construction;
it is not an extra hypothesis, and global CM/regularity is not added.
The same actual original ordered-top module extension class pushes along
a:B->N to original a(1) mod I N. Original GLOBAL sheaf epsilon is separate. -/
theorem projectivePulledLinearSection_exists_actual_affineKoszul_coefficientExt
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hproper : V.ideal.toIdeal ≠ ⊥)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+2) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = ((r+1 : ℕ) : WithBot ℕ∞))
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+2)) ℂ, c ≠ 0 ∧
      (∃ w : Fin (r+2) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+2) → ℂ, MvPolynomial.eval w c ≠ 0 →
        let I := (projectivePulledLinearSectionIdeal f V L w).map
          (affineChartPolynomialMap (K := ℂ)).toRingHom
        let C := MvPolynomial (Fin n) ℂ ⧸ I
        let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
        let H : Fin (r+1) → B := fun i => Ideal.Quotient.mk V.affineIdeal
          (affineChartPolynomialMap
            (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
        w 0 ≠ 0 ∧ _root_.IsReduced C ∧ Module.Finite ℂ C ∧
          Nonempty (projectivePulledLinearSectionScheme f V L hL w ≅ Spec (CommRingCat.of C)) ∧
          AlgebraicGeometry.IsReduced (projectivePulledLinearSectionScheme f V L hL w) ∧
          ∃ he : ∀ j : ℕ, 0 < j → (koszulComplex (Fintype.linearCombination B H)).ExactAt j,
            ∀ N : ModuleCat.{0} B,
              ∃ e : Ext.{0} (ModuleCat.of B (B ⧸ Ideal.span (Set.range H))) N (r+1) ≃ₗ[B]
                N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule B N)),
                ∀ a : B →ₗ[B] N,
                  e ((koszulExactTopExtCoefficientRepresentative r H he (ModuleCat.of B B)
                    (topKoszulCoordinate (r+1))).comp
                      (Ext.mk₀ (ModuleCat.ofHom a)) (add_zero _)) =
                    Submodule.Quotient.mk (a 1) := by
  obtain ⟨c,hc,hex,hcuts⟩ := projectivePulledLinearSection_exists_affineKoszul_exactAt
    (r := r+1) f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hred,hfin,hiso,hsch,he⟩ := hcuts w hw
  refine ⟨hw0,hred,hfin,hiso,hsch,he,?_⟩
  intro N
  refine ⟨koszulExactTopExtCoefficientRestrictionEquiv r _ he N,?_⟩
  intro a
  exact koszulExactTopExtCoefficientRestrictionEquiv_pushGenerator r _ he N a

end LinearStudy
