module
public import Linear.SchemeModuleInternalExtSourceExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Actual source connecting map on derived SHEAF Ext,computed using a
specified actual coefficient injective resolution and native snake boundary.
Independence of I is a separate obligation,not included in this definition. -/
def schemeModuleInternalExtSourceBoundaryViaResolution
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) :
    schemeModuleInternalExt S.X₁ N q ⟶ schemeModuleInternalExt S.X₃ N (q+1) :=
  (schemeModuleInternalExtInjectiveResolutionIso S.X₁ N q I).hom ≫
    (schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex).δ q (q+1) rfl ≫
      (schemeModuleInternalExtInjectiveResolutionIso S.X₃ N (q+1) I).inv

/-- The SAME actual connecting map commutes with the native snake boundary. -/
theorem schemeModuleInternalExtSourceBoundary_resolution_square
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) :
    schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q ≫
        (schemeModuleInternalExtInjectiveResolutionIso S.X₃ N (q+1) I).hom =
      (schemeModuleInternalExtInjectiveResolutionIso S.X₁ N q I).hom ≫
        (schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex).δ q (q+1) rfl := by
  unfold schemeModuleInternalExtSourceBoundaryViaResolution
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

end LinearStudy
