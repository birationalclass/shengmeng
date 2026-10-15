module
public import Linear.SchemeModuleOriginalCutCokernelTarget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
attribute [local irreducible] tildeKoszulOriginalCutCokernelCofork

/-- Compose the actual original cofork-point equality,original scheme
square and a specified native twist GENERICALLY,before specializing the
large original coordinate/presentation types. All maps retain their
original source and target. The original application constructs hM,g,hg
and tau rather than adding the desired final comparison as a premise. -/
def schemeModuleOriginalCutNativeTwistTargetIso (R : CommRingCat.{u})
    {r : ℕ} (H : Fin r → R) {X Z : Scheme.{u}}
    (j : Spec R ⟶ X) (i : Z ⟶ X)
    (g : Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range H))) ≅ Z)
    (hg : g.hom ≫ i =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))) ≫ j)
    (M : (Spec R).Modules) (hM : M = (tildeKoszulOriginalCutCokernelCofork R H).pt)
    (T : Z.Modules) (tau : SheafOfModules.unit Z.ringCatSheaf ≅ T) :
    (Scheme.Modules.pushforward j).obj M ≅ (Scheme.Modules.pushforward i).obj T :=
  (Scheme.Modules.pushforward j).mapIso (eqToIso hM) ≪≫
    schemeModuleOriginalCutCokernelTargetIso R H j i g hg ≪≫
      (Scheme.Modules.pushforward i).mapIso tau

end LinearStudy
