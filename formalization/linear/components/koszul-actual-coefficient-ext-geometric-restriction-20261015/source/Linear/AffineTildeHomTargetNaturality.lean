module
public import Linear.AffineTildeHomPrecompositionValues
public import Mathlib.LinearAlgebra.BilinearMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- SAME original global-Hom precomposition square for ANY original target
N. Reuse the actual library linear composition map,not a new model.
No invertibility/freeness/FP of the original target N is required. -/
theorem affineTildeHomTopPrecomposeSquare (R : CommRingCat.{u})
    (M' M N : ModuleCat.{u} R) (f : M' ⟶ M) :
    let H := schemeModuleHomModuleSheaf (tilde M) (tilde N)
    let H' := schemeModuleHomModuleSheaf (tilde M') (tilde N)
    letI : Module R Γ(H,⊤) := inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H))
    letI : Module R Γ(H',⊤) := inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H'))
    ModuleCat.ofHom (LinearMap.lcomp R N f.hom) ≫
        (affineTildeHomTopLinearEquiv R M' N).symm.toModuleIso.hom =
      (affineTildeHomTopLinearEquiv R M N).symm.toModuleIso.hom ≫
        moduleSpecΓFunctor.map (schemeModuleHomPrecompose ((tilde.functor R).map f)) := by
  let H := schemeModuleHomModuleSheaf (tilde M) (tilde N)
  let H' := schemeModuleHomModuleSheaf (tilde M') (tilde N)
  letI : Module R Γ(H,⊤) := inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H))
  letI : Module R Γ(H',⊤) := inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H'))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change (affineTildeHomTopLinearEquiv R M' N).symm ((LinearMap.lcomp R N f.hom) phi) =
    (schemeModuleHomPrecompose ((tilde.functor R).map f)).app ⊤
      ((affineTildeHomTopLinearEquiv R M N).symm phi)
  apply (affineTildeHomTopLinearEquiv R M' N).injective
  rw [LinearEquiv.apply_symm_apply, affineTildeHomTopLinearEquiv_precompose,
    LinearEquiv.apply_symm_apply]
  rfl

/-- The ACTUAL constructed internal-Hom iso commutes with ORIGINAL
precomposition for ANY original target N. The source FP conditions only
are required. No canonical-target freeness or local-frame premise. -/
theorem affineTildeFinitePresentationHomIso_precompose (R : CommRingCat.{u})
    (M' M N : ModuleCat.{u} R) [Module.FinitePresentation R M']
    [Module.FinitePresentation R M] (f : M' ⟶ M) :
    (tilde.functor R).map (ModuleCat.ofHom (LinearMap.lcomp R N f.hom)) ≫
        (affineTildeFinitePresentationHomIso R M' N).hom =
      (affineTildeFinitePresentationHomIso R M N).hom ≫
        schemeModuleHomPrecompose ((tilde.functor R).map f) := by
  apply ((tilde.adjunction (R := R)).homEquiv
    (ModuleCat.of R (M →ₗ[R] N))
    (schemeModuleHomModuleSheaf (tilde M') (tilde N))).injective
  rw [(tilde.adjunction (R := R)).homEquiv_naturality_left,
    (tilde.adjunction (R := R)).homEquiv_naturality_right]
  have hM : (tilde.adjunction (R := R)).homEquiv _ _
      (affineTildeFinitePresentationHomIso R M N).hom =
        (affineTildeHomTopLinearEquiv R M N).symm.toModuleIso.hom :=
    affineTildeFinitePresentationHomIso_sections R M N
  have hM' : (tilde.adjunction (R := R)).homEquiv _ _
      (affineTildeFinitePresentationHomIso R M' N).hom =
        (affineTildeHomTopLinearEquiv R M' N).symm.toModuleIso.hom :=
    affineTildeFinitePresentationHomIso_sections R M' N
  rw [hM', hM]
  exact affineTildeHomTopPrecomposeSquare R M' M N f

end LinearStudy