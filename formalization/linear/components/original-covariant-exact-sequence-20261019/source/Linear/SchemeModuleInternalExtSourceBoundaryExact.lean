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

/-- The actual original source map followed by the SAME connecting map is zero. -/
theorem schemeModuleInternalExtSourceMap_comp_boundary
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) :
    schemeModuleInternalExtSourceMap S.f N q ≫
      schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q = 0 := by
  let hT := schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex
  have hz : HomologicalComplex.homologyMap
      (schemeModuleHomCoefficientComplexMap S.f I.cocomplex) q ≫
        hT.δ q (q+1) rfl = 0 := hT.comp_δ q (q+1) rfl
  apply (cancel_mono (schemeModuleInternalExtInjectiveResolutionIso S.X₃ N (q+1) I).hom).1
  rw [zero_comp,Category.assoc,schemeModuleInternalExtSourceBoundary_resolution_square,
    ← Category.assoc,schemeModuleInternalExtSourceMap_resolution_square,Category.assoc,hz,
    comp_zero]

/-- The SAME connecting map followed by the actual next original source map is zero. -/
theorem schemeModuleInternalExtSourceBoundary_comp_map
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) :
    schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q ≫
      schemeModuleInternalExtSourceMap S.g N (q+1) = 0 := by
  let hT := schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex
  have hz : hT.δ q (q+1) rfl ≫ HomologicalComplex.homologyMap
      (schemeModuleHomCoefficientComplexMap S.g I.cocomplex) (q+1) = 0 :=
    hT.δ_comp q (q+1) rfl
  apply (cancel_mono (schemeModuleInternalExtInjectiveResolutionIso S.X₂ N (q+1) I).hom).1
  rw [zero_comp,Category.assoc,schemeModuleInternalExtSourceMap_resolution_square,
    ← Category.assoc,schemeModuleInternalExtSourceBoundary_resolution_square,
    Category.assoc,hz,comp_zero]

/-- ACTUAL derived SHEAF Ext is exact immediately before its actual source boundary. -/
theorem schemeModuleInternalExtSourceBoundary_exact_before
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) :
    (ShortComplex.mk (schemeModuleInternalExtSourceMap S.f N q)
      (schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q)
      (schemeModuleInternalExtSourceMap_comp_boundary S hS N I q)).Exact := by
  let hT := schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex
  let e : ShortComplex.mk _ _ (schemeModuleInternalExtSourceMap_comp_boundary S hS N I q) ≅
      ShortComplex.mk _ _ (hT.comp_δ q (q+1) rfl) :=
    ShortComplex.isoMk
      (schemeModuleInternalExtInjectiveResolutionIso S.X₂ N q I)
      (schemeModuleInternalExtInjectiveResolutionIso S.X₁ N q I)
      (schemeModuleInternalExtInjectiveResolutionIso S.X₃ N (q+1) I)
      (schemeModuleInternalExtSourceMap_resolution_square S.f N q I).symm
      (schemeModuleInternalExtSourceBoundary_resolution_square S hS N I q).symm
  exact ShortComplex.exact_of_iso e.symm (hT.homology_exact₃ q (q+1) rfl)

/-- ACTUAL derived SHEAF Ext is exact immediately after its actual source boundary. -/
theorem schemeModuleInternalExtSourceBoundary_exact_after
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) :
    (ShortComplex.mk (schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q)
      (schemeModuleInternalExtSourceMap S.g N (q+1))
      (schemeModuleInternalExtSourceBoundary_comp_map S hS N I q)).Exact := by
  let hT := schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex
  let e : ShortComplex.mk _ _ (schemeModuleInternalExtSourceBoundary_comp_map S hS N I q) ≅
      ShortComplex.mk _ _ (hT.δ_comp q (q+1) rfl) :=
    ShortComplex.isoMk
      (schemeModuleInternalExtInjectiveResolutionIso S.X₁ N q I)
      (schemeModuleInternalExtInjectiveResolutionIso S.X₃ N (q+1) I)
      (schemeModuleInternalExtInjectiveResolutionIso S.X₂ N (q+1) I)
      (schemeModuleInternalExtSourceBoundary_resolution_square S hS N I q).symm
      (schemeModuleInternalExtSourceMap_resolution_square S.g N (q+1) I).symm
  exact ShortComplex.exact_of_iso e.symm (hT.homology_exact₁ q (q+1) rfl)

end LinearStudy
