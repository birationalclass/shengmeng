module
public import Linear.SchemeModuleSpecOpenSections
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
/-- Actual scalar transport for an arbitrary Spec-chart open. -/
theorem schemeModuleSpecOpenSectionsEquiv_smul
    (W : (Spec R).Opens) (U : X.Opens) (himage : f ''ᵁ W = U)
    (r : Γ(X,U)) (x : Γ(M,U)) :
    schemeModuleSpecOpenSectionsEquiv M f W U himage (r • x) =
      (f.appIso W).hom (X.presheaf.map (eqToHom himage).op r) •
        schemeModuleSpecOpenSectionsEquiv M f W U himage x := by
  let i : op U ⟶ op (f ''ᵁ W) := (eqToHom himage).op
  change (M.restrictAppIso f W).inv (M.presheaf.map i (r • x)) =
    (f.appIso W).hom (X.presheaf.map i r) •
      (M.restrictAppIso f W).inv (M.presheaf.map i x)
  have hs := M.val.map_smul i r x
  change M.presheaf.map i (r • x) = X.presheaf.map i r • M.presheaf.map i x at hs
  rw [hs]
  exact congr($(M.smul_restrictAppIso_inv f W (X.presheaf.map i r)) (M.presheaf.map i x))
end LinearStudy
