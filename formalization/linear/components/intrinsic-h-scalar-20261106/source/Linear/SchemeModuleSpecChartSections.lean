module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} {R : CommRingCat.{u}}
variable (M : X.Modules) (f : Spec R ⟶ X) [IsOpenImmersion f]
variable (U : X.Opens) (himage : f ''ᵁ ⊤ = U)

/-- SAME actual module sections, transported along the given Spec chart. -/
def schemeModuleSpecChartSectionsEquiv : Γ(M,U) ≃+ Γ(M.restrict f,⊤) :=
  Iso.addCommGroupIsoToAddEquiv
    (M.presheaf.mapIso (eqToIso himage).op ≪≫ (M.restrictAppIso f ⊤).symm)

/-- Actual scalar relation at the same chart, before bundling an R-linear map. -/
theorem schemeModuleSpecChartSectionsEquiv_smul
    (φ : R ⟶ Γ(X,U))
    (hφ : φ ≫ f.appLE U ⊤ (by rw [← himage]; exact (f.preimage_image_eq ⊤).ge) =
      (Scheme.ΓSpecIso R).inv)
    (r : R) (x : Γ(M,U)) :
    schemeModuleSpecChartSectionsEquiv M f U himage (φ r • x) =
      (Scheme.ΓSpecIso R).inv r • schemeModuleSpecChartSectionsEquiv M f U himage x := by
  let i : op U ⟶ op (f ''ᵁ ⊤) := (eqToHom himage).op
  have hr : X.presheaf.map i (φ r) = (f.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r) := by
    apply (f.appIso ⊤).commRingCatIsoToRingEquiv.injective
    change (f.appIso ⊤).hom (X.presheaf.map i (φ r)) =
      (f.appIso ⊤).hom ((f.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))
    rw [Iso.inv_hom_id_apply]
    change (X.presheaf.map i ≫ (f.appIso ⊤).hom) (φ r) = _
    have hf : X.presheaf.map i ≫ (f.appIso ⊤).hom =
        f.appLE U ⊤ (by rw [← himage]; exact (f.preimage_image_eq ⊤).ge) := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE']
    rw [hf]
    simpa using congr($(hφ) r)
  change (M.restrictAppIso f ⊤).inv (M.presheaf.map i (φ r • x)) = _
  have hs := M.val.map_smul i (φ r) x
  change M.presheaf.map i (φ r • x) = X.presheaf.map i (φ r) • M.presheaf.map i x at hs
  rw [hs,hr]
  change (M.restrictAppIso f ⊤).inv
      ((f.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r) • M.presheaf.map i x) = _
  rfl

end LinearStudy
