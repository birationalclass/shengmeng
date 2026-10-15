module
public import Linear.ProjectivePulledWholeCutLiteralAugmentationProof
public import Linear.ParameterFamilyDependentCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
variable {n r : ℕ}

/-- ORIGINAL proof value:derive ONE NONEMPTY parameter open BEFORE ALL
integer twists,on which actual whole-cut native-twist chain augmentations
satisfy the original chart-adjoint/target-identification formula.
No desired map formula or target comparison is an added hypothesis.
Canonical geometric augmentation,epsilon and the original lemmas remain open. -/
def projectivePulledLinearSectionWholeCutLiteralAugmentationFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  let build := fun (w : Fin (r+1) → ℂ)
    (hc : projectivePulledWholeCutNativeAugmentationConditions f V L hL w) (k : ℤ) =>
      projectivePulledWholeCutLiteralAugmentationProof f V L hL w k hc
  parameterFamily_of_dependent_cover
    (fun c : MvPolynomial (Fin (r+1)) ℂ => c ≠ 0)
    (fun c : MvPolynomial (Fin (r+1)) ℂ =>
      ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0)
    (fun (c : MvPolynomial (Fin (r+1)) ℂ) (w : Fin (r+1) → ℂ) =>
      MvPolynomial.eval w c ≠ 0)
    (projectivePulledWholeCutNativeAugmentationConditions f V L hL) _
    (projectivePulledLinearSection_exists_wholeCutNativeAugmentationConditions
      f V hq hf hV L hL hinj hfinite x0 hx0) build

end LinearStudy
