module
public import Linear.SchemeModuleSpecOpenSectionsScalar
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
/-- Scalars restricted from the full SAME Spec chart act by the original ring R
under actual open-chart section transport. Its hypothesis is the concrete
structure-sheaf scalar square, not section-map compatibility. -/
theorem schemeModuleSpecOpenSectionsEquiv_smul_fromTop
    (W : (Spec R).Opens) (φ : R ⟶ Γ(X,f ''ᵁ ⊤))
    (hφ : φ ≫ (f.appIso ⊤).hom = (Scheme.ΓSpecIso R).inv)
    (r : R) (x : Γ(M,f ''ᵁ W)) :
    schemeModuleSpecOpenSectionsEquiv M f W (f ''ᵁ W) rfl
      (X.presheaf.map (homOfLE (Scheme.Hom.image_mono f (show W ≤ ⊤ from le_top))).op (φ r) • x) =
    r • schemeModuleSpecOpenSectionsEquiv M f W (f ''ᵁ W) rfl x := by
  have hn : φ ≫ X.presheaf.map (homOfLE (Scheme.Hom.image_mono f (show W ≤ ⊤ from le_top))).op ≫
      (f.appIso W).hom =
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map W.leTop.op := by
    have H : X.presheaf.map (homOfLE (Scheme.Hom.image_mono f (show W ≤ ⊤ from le_top))).op ≫
        (f.appIso W).hom = (f.appIso ⊤).hom ≫ (Spec R).presheaf.map W.leTop.op :=
      f.appIso_hom_naturality W.leTop.op
    rw [H, ← Category.assoc,hφ]
  have hc : (f.appIso W).hom
      (X.presheaf.map (homOfLE (Scheme.Hom.image_mono f (show W ≤ ⊤ from le_top))).op (φ r)) =
    (Spec R).presheaf.map W.leTop.op ((Scheme.ΓSpecIso R).inv r) := by
    simpa only [ConcreteCategory.comp_apply] using congr($(hn) r)
  have H := schemeModuleSpecOpenSectionsEquiv_smul M f W (f ''ᵁ W) rfl
    (X.presheaf.map (homOfLE (Scheme.Hom.image_mono f (show W ≤ ⊤ from le_top))).op (φ r)) x
  change _ = (f.appIso W).hom (X.presheaf.map (𝟙 (op (f ''ᵁ W))) _) • _ at H
  rw [X.presheaf.map_id] at H
  simp only [ConcreteCategory.id_apply] at H
  rw [hc] at H
  simpa only [Scheme.Modules.smul_Spec_def] using H
end LinearStudy
