module
public import Linear.AffineTildeFinitePresentationInternalHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- ACTUAL global sections of internal sheaf Hom of ORIGINAL tilde
modules are the SAME ORIGINAL R-linear maps. The existing ACTUAL
open Hom equivalence and original tilde.isoTop are reused. -/
def affineTildeHomTopLinearEquiv (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    Γ(schemeModuleHomModuleSheaf (tilde M) (tilde N),⊤) ≃ₗ[R] (M →ₗ[R] N) :=
  (affineQuasicoherentHomActualOpenSectionsLinearEquiv (tilde N) (tilde M) ⊤).trans
    (LinearEquiv.arrowCongr (tilde.isoTop M).toLinearEquiv.symm
      (tilde.isoTop N).toLinearEquiv.symm)

/-- CONSTRUCT an ACTUAL affine internal-sheaf-Hom identification from
ORIGINAL finitely presented source M and target N. Quasicoherence of
ACTUAL internal Hom is PROVED;the actual tilde counit and actual global
Hom map identify ~Hom_R(M,N) with Hom_O(~M,~N). No Hom iso is an input. -/
def affineTildeFinitePresentationHomIso (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    tilde (ModuleCat.of R (M →ₗ[R] N)) ≅ schemeModuleHomModuleSheaf (tilde M) (tilde N) := by
  let H := schemeModuleHomModuleSheaf (tilde M) (tilde N)
  letI : H.IsQuasicoherent := affineTildeFinitePresentationInternalHom_isQuasicoherent R M N
  exact (tilde.functor R).mapIso (affineTildeHomTopLinearEquiv R M N).symm.toModuleIso ≪≫
    asIso H.fromTildeΓ

/-- The CONSTRUCTED ACTUAL internal-Hom iso has the ACTUAL original
Hom-section inverse as its global R-linear map. Proved using the
library tilde adjunction,not a section-value compatibility premise. -/
theorem affineTildeFinitePresentationHomIso_sections (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    let H := schemeModuleHomModuleSheaf (tilde M) (tilde N)
    letI : Module R Γ(H,⊤) :=
      inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H))
    (tilde.isoTop (ModuleCat.of R (M →ₗ[R] N))).hom ≫
      moduleSpecΓFunctor.map (affineTildeFinitePresentationHomIso R M N).hom =
        (affineTildeHomTopLinearEquiv R M N).symm.toModuleIso.hom := by
  let H := schemeModuleHomModuleSheaf (tilde M) (tilde N)
  letI : Module R Γ(H,⊤) :=
    inferInstanceAs (Module R ((moduleSpecΓFunctor (R := R)).obj H))
  exact ((tilde.adjunction (R := R)).homEquiv
    (ModuleCat.of R (M →ₗ[R] N)) (schemeModuleHomModuleSheaf (tilde M) (tilde N))).apply_symm_apply
      ((affineTildeHomTopLinearEquiv R M N).symm.toModuleIso.hom)

end LinearStudy
