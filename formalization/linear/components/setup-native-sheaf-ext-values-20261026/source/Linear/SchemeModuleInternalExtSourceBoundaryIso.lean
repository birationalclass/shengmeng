module
public import Linear.SchemeModuleInternalExtSourceBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Dimension shifting for ACTUAL derived SHEAF Ext when the two explicitly
stated middle terms vanish. No vanishing for locally free sheaves is assumed. -/
def schemeModuleInternalExtSourceBoundaryIsoViaResolution
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ)
    (hi : IsZero (schemeModuleInternalExt S.X₂ N q))
    (hj : IsZero (schemeModuleInternalExt S.X₂ N (q+1))) :
    schemeModuleInternalExt S.X₁ N q ≅ schemeModuleInternalExt S.X₃ N (q+1) :=
  schemeModuleInternalExtInjectiveResolutionIso S.X₁ N q I ≪≫
    (schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex).δIso q (q+1) rfl
      (IsZero.of_iso hi (schemeModuleInternalExtInjectiveResolutionIso S.X₂ N q I).symm)
      (IsZero.of_iso hj (schemeModuleInternalExtInjectiveResolutionIso S.X₂ N (q+1) I).symm) ≪≫
        (schemeModuleInternalExtInjectiveResolutionIso S.X₃ N (q+1) I).symm

/-- The dimension-shifting iso uses the SAME actual connecting morphism. -/
theorem schemeModuleInternalExtSourceBoundaryIsoViaResolution_hom
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ)
    (hi : IsZero (schemeModuleInternalExt S.X₂ N q))
    (hj : IsZero (schemeModuleInternalExt S.X₂ N (q+1))) :
    (schemeModuleInternalExtSourceBoundaryIsoViaResolution S hS N I q hi hj).hom =
      schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q := rfl

end LinearStudy
