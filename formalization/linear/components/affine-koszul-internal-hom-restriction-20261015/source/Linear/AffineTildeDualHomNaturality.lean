module
public import Linear.AffineTildeHomPrecompositionValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- The ACTUAL original module-valued global Hom square commutes for
precomposition by the SAME original linear map f. No square is assumed. -/
theorem affineTildeDualHomTopPrecomposeSquare (R : CommRingCat.{u})
    (M' M : ModuleCat.{u} R) (f : M' ⟶ M) :
    let H := schemeModuleHomModuleSheaf (tilde M) (tilde (ModuleCat.of R R))
    let H' := schemeModuleHomModuleSheaf (tilde M') (tilde (ModuleCat.of R R))
    letI : Module R Γ(H,⊤) := inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H))
    letI : Module R Γ(H',⊤) := inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H'))
    ModuleCat.ofHom f.hom.dualMap ≫
        (affineTildeHomTopLinearEquiv R M' (ModuleCat.of R R)).symm.toModuleIso.hom =
      (affineTildeHomTopLinearEquiv R M (ModuleCat.of R R)).symm.toModuleIso.hom ≫
        moduleSpecΓFunctor.map (schemeModuleHomPrecompose ((tilde.functor R).map f)) := by
  let H := schemeModuleHomModuleSheaf (tilde M) (tilde (ModuleCat.of R R))
  let H' := schemeModuleHomModuleSheaf (tilde M') (tilde (ModuleCat.of R R))
  letI : Module R Γ(H,⊤) := inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H))
  letI : Module R Γ(H',⊤) := inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H'))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change (affineTildeHomTopLinearEquiv R M' (ModuleCat.of R R)).symm (f.hom.dualMap phi) =
    (schemeModuleHomPrecompose ((tilde.functor R).map f)).app ⊤
      ((affineTildeHomTopLinearEquiv R M (ModuleCat.of R R)).symm phi)
  apply (affineTildeHomTopLinearEquiv R M' (ModuleCat.of R R)).injective
  rw [LinearEquiv.apply_symm_apply, affineTildeHomTopLinearEquiv_precompose,
    LinearEquiv.apply_symm_apply]
  rfl

/-- The CONSTRUCTED ACTUAL affine dual/internal-Hom sheaf iso commutes
with precomposition by the SAME original f. The tilde adjunction and
proved global-section square prove equality of ACTUAL sheaf morphisms.
Only the two ORIGINAL modules being finitely presented is required. -/
theorem affineTildeFinitePresentationDualHomIso_precompose (R : CommRingCat.{u})
    (M' M : ModuleCat.{u} R) [Module.FinitePresentation R M']
    [Module.FinitePresentation R M] (f : M' ⟶ M) :
    (tilde.functor R).map (ModuleCat.ofHom f.hom.dualMap) ≫
        (affineTildeFinitePresentationHomIso R M' (ModuleCat.of R R)).hom =
      (affineTildeFinitePresentationHomIso R M (ModuleCat.of R R)).hom ≫
        schemeModuleHomPrecompose ((tilde.functor R).map f) := by
  apply ((tilde.adjunction (R := R)).homEquiv
    (ModuleCat.of R (Module.Dual R M))
    (schemeModuleHomModuleSheaf (tilde M') (tilde (ModuleCat.of R R)))).injective
  rw [(tilde.adjunction (R := R)).homEquiv_naturality_left,
    (tilde.adjunction (R := R)).homEquiv_naturality_right]
  have hM : (tilde.adjunction (R := R)).homEquiv _ _
      (affineTildeFinitePresentationHomIso R M (ModuleCat.of R R)).hom =
        (affineTildeHomTopLinearEquiv R M (ModuleCat.of R R)).symm.toModuleIso.hom :=
    affineTildeFinitePresentationHomIso_sections R M (ModuleCat.of R R)
  have hM' : (tilde.adjunction (R := R)).homEquiv _ _
      (affineTildeFinitePresentationHomIso R M' (ModuleCat.of R R)).hom =
        (affineTildeHomTopLinearEquiv R M' (ModuleCat.of R R)).symm.toModuleIso.hom :=
    affineTildeFinitePresentationHomIso_sections R M' (ModuleCat.of R R)
  rw [hM', hM]
  exact affineTildeDualHomTopPrecomposeSquare R M' M f

end LinearStudy