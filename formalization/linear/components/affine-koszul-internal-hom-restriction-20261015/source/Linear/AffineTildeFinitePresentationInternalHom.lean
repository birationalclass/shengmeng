module
public import Linear.AffineFinitePresentationInternalHomQuasicoherent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- For SAME original finitely presented affine source module M and
original target N,the ACTUAL internal sheaf Hom of the ACTUAL tilde
sheaves is quasicoherent. Finite presentation of ACTUAL global sections
is transported from original M using the library ACTUAL tilde.isoTop;
no internal-Hom comparison/quasicoherence certificate is assumed. -/
theorem affineTildeFinitePresentationInternalHom_isQuasicoherent
    (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    (schemeModuleHomModuleSheaf (tilde M) (tilde N)).IsQuasicoherent := by
  letI : Module.FinitePresentation R ((moduleSpecΓFunctor (R := R)).obj (tilde M)) :=
    Module.FinitePresentation.of_equiv (tilde.isoTop M).toLinearEquiv
  exact affineFinitePresentationInternalHom_isQuasicoherent (tilde M) (tilde N)

end LinearStudy
