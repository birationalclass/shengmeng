module
public import Linear.SchemeModuleHomShortComplexSourceMap
public import Linear.SchemeModuleInternalExtSourceBoundaryNaturality
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- ACTUAL derived SHEAF Ext source boundary is natural in morphisms of source short exact sequences. -/
theorem schemeModuleInternalExtSourceBoundaryViaResolution_sourceNaturality
    {S T : ShortComplex X.Modules} (phi : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) :
    schemeModuleInternalExtSourceBoundaryViaResolution T hT N I q ≫
        schemeModuleInternalExtSourceMap phi.τ₃ N (q+1) =
      schemeModuleInternalExtSourceMap phi.τ₁ N q ≫
        schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q := by
  let hI := schemeModuleHomSourceShortComplex_shortExact T hT I.cocomplex
  let hJ := schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex
  have hdelta := HomologicalComplex.HomologySequence.δ_naturality
    (schemeModuleHomShortComplexSourceMap phi I.cocomplex) hI hJ q (q+1) rfl
  have hd : hI.δ q (q+1) rfl ≫
      HomologicalComplex.homologyMap (schemeModuleHomCoefficientComplexMap phi.τ₃ I.cocomplex) (q+1) =
      HomologicalComplex.homologyMap (schemeModuleHomCoefficientComplexMap phi.τ₁ I.cocomplex) q ≫
        hJ.δ q (q+1) rfl := hdelta
  apply (cancel_mono (schemeModuleInternalExtInjectiveResolutionIso S.X₃ N (q+1) I).hom).1
  rw [Category.assoc,schemeModuleInternalExtSourceMap_resolution_square,← Category.assoc,
    schemeModuleInternalExtSourceBoundary_resolution_square,Category.assoc]
  erw [hd]
  rw [← Category.assoc,← schemeModuleInternalExtSourceMap_resolution_square,Category.assoc,
    ← schemeModuleInternalExtSourceBoundary_resolution_square,← Category.assoc]
/-- The SAME naturality equation for the actual canonical,resolution-independent source boundary. -/
theorem schemeModuleInternalExtSourceBoundary_sourceNaturality
    {S T : ShortComplex X.Modules} (phi : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (N : X.Modules) (q : ℕ) :
    schemeModuleInternalExtSourceBoundary T hT N q ≫
        schemeModuleInternalExtSourceMap phi.τ₃ N (q+1) =
      schemeModuleInternalExtSourceMap phi.τ₁ N q ≫
        schemeModuleInternalExtSourceBoundary S hS N q := by
  rw [schemeModuleInternalExtSourceBoundary_eq_viaResolution T hT N (injectiveResolution N) q,
    schemeModuleInternalExtSourceBoundary_eq_viaResolution S hS N (injectiveResolution N) q]
  exact schemeModuleInternalExtSourceBoundaryViaResolution_sourceNaturality phi hS hT N
    (injectiveResolution N) q
end LinearStudy
