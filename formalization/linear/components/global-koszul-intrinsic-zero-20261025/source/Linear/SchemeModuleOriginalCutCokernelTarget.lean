module
public import Linear.SchemeModuleOriginalCutStructurePushforward
public import Linear.TildeKoszulOriginalCutCofork
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
attribute [local irreducible] tildeKoszulOriginalCutCokernelCofork

/-- Identify the ACTUAL original chart cofork's pushed point with the
WHOLE cut structure sheaf along its ACTUAL map into the SAME ambient.
Use the proved original cofork-point equality before specializing large
objects. The scheme iso and original square are explicit generic inputs. -/
def schemeModuleOriginalCutCokernelTargetIso (R : CommRingCat.{u})
    {r : ℕ} (H : Fin r → R) {X Z : Scheme.{u}}
    (j : Spec R ⟶ X) (i : Z ⟶ X)
    (g : Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range H))) ≅ Z)
    (hg : g.hom ≫ i =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))) ≫ j) :
    (Scheme.Modules.pushforward j).obj (tildeKoszulOriginalCutCokernelCofork R H).pt ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  (Scheme.Modules.pushforward j).mapIso
    (eqToIso (tildeKoszulOriginalCutCokernelCofork_point R H)) ≪≫
      schemeModuleOriginalCutStructurePushforwardIso g _ j i hg

end LinearStudy