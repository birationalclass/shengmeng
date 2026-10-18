module
public import Linear.AffineKoszulGeometricRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
/-- ACTUAL highest internal-Hom differential cokernel is the original geometric cut coefficient i_*i^*tilde N. Exactness and epimorphy are already PROVED for arbitrary N. -/
def affineKoszulHomGeometricCokernelIso :
    cokernel (schemeModuleHomPrecompose (N := tilde N) ((tilde.functor R).map (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) p)))) ≅
      (affineKoszulHomGeometricRestrictionPresentation R N p H).X₃ := by
  haveI := affineKoszulHomGeometricRestrictionPresentation_epi R N p H
  exact (cokernelIsCokernel (schemeModuleHomPrecompose (N := tilde N) ((tilde.functor R).map (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) p))))).coconePointUniqueUpToIso (affineKoszulHomGeometricRestrictionPresentation_exact R N p H).gIsCokernel
/-- SAME quotient projection becomes EXACTLY the original geometric coefficient restriction. -/
theorem affineKoszulHomGeometricCokernelIso_projection :
    cokernel.π (schemeModuleHomPrecompose (N := tilde N) ((tilde.functor R).map (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) p)))) ≫
        (affineKoszulHomGeometricCokernelIso R N p H).hom =
      (affineKoszulHomGeometricRestrictionPresentation R N p H).g := by
  have := affineKoszulHomGeometricRestrictionPresentation_epi R N p H
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (schemeModuleHomPrecompose (N := tilde N) ((tilde.functor R).map (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) p)))))
    (affineKoszulHomGeometricRestrictionPresentation_exact R N p H).gIsCokernel
    WalkingParallelPair.one
end LinearStudy
