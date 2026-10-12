module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

/-- Restriction of the ACTUAL global pushforward to an ORIGINAL open
is the ACTUAL pushforward of the original restricted morphism and module.
The map is induced by the real inverse-image/image open equality. -/
def schemeModulePushforwardOpenRestrictionIso
    (f : X ⟶ Y) (U : Y.Opens) (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun V => ?_) ?_
  · refine ModuleCat.isoMk
      (M.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U V.unop)).op) ?_
    intro r
    ext x
    symm
    change M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
        ((f.app (U.ι ''ᵁ V.unop) ((U.ι.appIso V.unop).inv r)) •
          (show Γ(M,f ⁻¹ᵁ (U.ι ''ᵁ V.unop)) from x)) =
      (show Γ(X,(f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V.unop)) from
        (((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ V.unop)).inv
          ((f ∣_ U).app V.unop r))) •
        M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
          (show Γ(M,f ⁻¹ᵁ (U.ι ''ᵁ V.unop)) from x)
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, ConcreteCategory.id_apply]
    rw [Scheme.Modules.map_smul, morphismRestrict_app, ConcreteCategory.comp_apply]
    rfl
  · intro V W i
    ext x
    change M.presheaf.map _ (M.presheaf.map _ x) =
      M.presheaf.map _ (M.presheaf.map _ x)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

end LinearStudy
