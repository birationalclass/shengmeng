module
public import Linear.TildeComplexExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R S : CommRingCat.{u}}

/-- The actual global sections of an affine pushforward agree with the
original module with scalars restricted along the actual ring map. -/
def tildePushforwardGlobalIso (φ : R ⟶ S) (M : ModuleCat.{u} S) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) ≅
      (ModuleCat.restrictScalars φ.hom).obj M := by
  let F : TopCat.Sheaf (ModuleCat.{u} R) (Spec R) ⥤ ModuleCat.{u} R :=
    TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)
  let e := F.mapIso ((pushforwardCompModulesSpecToSheafIso φ).app (tilde M))
  exact e ≪≫ (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop M).symm

/-- A genuine native sheaf isomorphism, rather than an assumed compatibility
of tilde and affine pushforward. -/
def tildePushforwardIso (φ : R ⟶ S) (M : ModuleCat.{u} S) :
    tilde ((ModuleCat.restrictScalars φ.hom).obj M) ≅
      (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) := by
  letI : IsIso (tilde M).fromTildeΓ :=
    isIso_fromTildeΓ_iff.mpr ⟨M,⟨Iso.refl _⟩⟩
  letI := isIso_fromTildeΓ_pushforward φ (tilde M)
  exact (tilde.functor R).mapIso (tildePushforwardGlobalIso φ M).symm ≪≫
    asIso ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)).fromTildeΓ

end LinearStudy
