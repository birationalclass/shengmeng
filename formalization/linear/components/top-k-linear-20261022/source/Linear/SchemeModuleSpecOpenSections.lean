module
public import Linear.SchemeModuleSpecChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} {R : CommRingCat.{u}}
variable (M : X.Modules) (f : Spec R ⟶ X) [IsOpenImmersion f]
/-- Transport SAME module sections on an arbitrary Spec-chart open, not only the full chart. -/
def schemeModuleSpecOpenSectionsEquiv
    (W : (Spec R).Opens) (U : X.Opens) (himage : f ''ᵁ W = U) :
    Γ(M,U) ≃+ Γ(M.restrict f,W) :=
  Iso.addCommGroupIsoToAddEquiv
    (M.presheaf.mapIso (eqToIso himage).op ≪≫ (M.restrictAppIso f W).symm)
/-- The real restriction square commutes under the actual open-immersion section transport. -/
theorem schemeModuleSpecOpenSectionsEquiv_restrict
    (W V : (Spec R).Opens) (U T : X.Opens)
    (hW : f ''ᵁ W = U) (hV : f ''ᵁ V = T) (hWV : W ≤ V)
    (x : Γ(M,T)) :
    schemeModuleSpecOpenSectionsEquiv M f W U hW
      (M.presheaf.map (homOfLE (by rw [←hW,←hV]; exact Scheme.Hom.image_mono f hWV)).op x) =
    (M.restrict f).presheaf.map (homOfLE hWV).op
      (schemeModuleSpecOpenSectionsEquiv M f V T hV x) := by
  subst U
  subst T
  change (M.restrictAppIso f W).inv
      (M.presheaf.map (𝟙 (op (f ''ᵁ W)))
        (M.presheaf.map (homOfLE (Scheme.Hom.image_mono f hWV)).op x)) =
    (M.restrict f).presheaf.map (homOfLE hWV).op
      ((M.restrictAppIso f V).inv (M.presheaf.map (𝟙 (op (f ''ᵁ V))) x))
  rw [M.presheaf.map_id, M.presheaf.map_id]
  simpa only [ConcreteCategory.id_apply, ConcreteCategory.comp_apply] using
    congr($(M.restrictAppIso_inv_map f (homOfLE hWV).op) x).symm

end LinearStudy
