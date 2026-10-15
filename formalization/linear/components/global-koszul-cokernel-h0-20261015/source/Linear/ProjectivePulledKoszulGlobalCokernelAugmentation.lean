module
public import Linear.ProjectivePulledKoszulGlobalExact
public import Linear.ChainActualCokernelAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] projectivePulledLinearKoszulComplex
variable {n r : ℕ}

/-- Under the SAME ORIGINAL nonzero-ideal geometric hypotheses,derive
that the ACTUAL canonical categorical-cokernel augmentation of the SAME
named ORIGINAL GLOBAL Koszul is a quasi-isomorphism,on a nonempty
parameter open BEFORE ALL integer twists. The cokernel is ACTUAL,not a
certificate. Identification with the SAME original finite-cut structure
sheaf remains OPEN and is NOT asserted by this theorem. -/
theorem projectivePulledLinearSection_exists_globalCokernelAugmentation_quasiIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hproper : V.ideal.toIdeal ≠ ⊥)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞))
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        ∀ k : ℤ,QuasiIso (originalChainCokernelAugmentation
          (projectivePulledLinearKoszulComplex f V L hL w k)) := by
  obtain ⟨c,hc,hex,he⟩ := projectivePulledLinearSection_exists_globalKoszul_exactAt
    f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw k
  exact originalChainCokernelAugmentation_quasiIso _ (he w hw k)

end LinearStudy
