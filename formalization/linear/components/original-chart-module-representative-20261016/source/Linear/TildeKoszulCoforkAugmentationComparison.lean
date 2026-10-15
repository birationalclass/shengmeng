module
public import Linear.MappedChainCokernelAugmentationSquare
public import Linear.TildeKoszulOriginalCutCofork
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- The ACTUAL original affine quotient-cofork augmentation is EXACTLY
the SAME native tilde image of the ACTUAL module quotient augmentation,
followed by the constructed original cut-structure-sheaf target iso.
This is a whole chain-map equality,not an assumed representative identity. -/
theorem tildeKoszulOriginalCoforkAugmentation_eq_mappedModule
    (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
        (tildeKoszulOriginalCutCokernelCofork R H) =
      mappedOriginalChainAugmentation (tilde.functor R)
          (koszulComplex (Fintype.linearCombination R H)) (functionKoszulAugmentationMap H) ≫
        (ChainComplex.single₀ (Spec R).Modules).map
          (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,ChainComplex.single₀_map_f_zero,
    mappedOriginalChainAugmentation_f_zero,originalChainCoforkAugmentation,
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  simp [tildeKoszulOriginalCutCokernelCofork,tildeKoszulPresentation,
    functionKoszulAugmentationMap]

end LinearStudy
