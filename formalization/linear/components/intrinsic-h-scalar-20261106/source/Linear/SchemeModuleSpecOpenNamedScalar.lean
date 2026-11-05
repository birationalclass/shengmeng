module
public import Linear.SchemeModuleSpecOpenSectionsRestrictedScalar
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
/-- The same scalar-compatibility formula with named actual image opens.
The concrete top-chart structure-ring square is the only scalar hypothesis. -/
theorem schemeModuleSpecOpenSectionsEquiv_smul_namedImages
    (W : (Spec R).Opens) (U T : X.Opens)
    (hW : f ''ᵁ W = U) (hT : f ''ᵁ ⊤ = T)
    (φ : R ⟶ Γ(X,T))
    (hφ : φ ≫ X.presheaf.map (eqToHom hT).op ≫ (f.appIso ⊤).hom =
      (Scheme.ΓSpecIso R).inv)
    (r : R) (x : Γ(M,U)) :
    schemeModuleSpecOpenSectionsEquiv M f W U hW
      (X.presheaf.map (homOfLE (show U ≤ T from by rw [←hW,←hT]; exact Scheme.Hom.image_mono f le_top)).op (φ r) • x) =
    r • schemeModuleSpecOpenSectionsEquiv M f W U hW x := by
  subst U
  subst T
  change φ ≫ X.presheaf.map (𝟙 (op (f ''ᵁ ⊤))) ≫ (f.appIso ⊤).hom = _ at hφ
  rw [X.presheaf.map_id,Category.id_comp] at hφ
  exact schemeModuleSpecOpenSectionsEquiv_smul_fromTop M f W φ hφ r x
end LinearStudy
