module
public import Linear.SchemeModuleInternalHomComplex
public import Linear.SchemeModuleHomOpenImmersionIso
public import Linear.SchemeModuleOpenRestrictionExact
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
/-- Actual internal Hom from a zero source is zero, by the existing additive contravariant Hom functor. -/
theorem schemeModuleHomModuleSheaf_isZero_of_source {X : Scheme.{u}}
    (P N : X.Modules) (hP : IsZero P) : IsZero (schemeModuleHomModuleSheaf P N) :=
  (schemeModuleInternalHomFunctor X N).map_isZero hP.op
/-- The SAME actual Hom sheaf vanishes on an actual open where its original source vanishes; no quasi-coherence assumption on N. -/
theorem schemeModuleHomModuleSheaf_open_isZero_of_source {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (P N : X.Modules) (hP : IsZero (P.restrict j)) :
    IsZero ((schemeModuleHomModuleSheaf P N).restrict j) :=
  (schemeModuleHomModuleSheaf_isZero_of_source (P.restrict j) (N.restrict j) hP).of_iso
    (schemeModuleHomOpenImmersionIso P N j)
/-- Every actual subobject of the original Hom sheaf has the SAME open support bound. This applies to actual cycles and boundaries, not just the Hom terms. -/
theorem schemeModuleSubHom_open_isZero_of_source {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (P N M : X.Modules)
    (g : M ⟶ schemeModuleHomModuleSheaf P N) [Mono g] (hP : IsZero (P.restrict j)) :
    IsZero (M.restrict j) := by
  letI := schemeModuleOpenRestriction_preservesFiniteLimits j
  exact IsZero.of_mono ((Scheme.Modules.restrictFunctor j).map g)
    (schemeModuleHomModuleSheaf_open_isZero_of_source j P N hP)
end LinearStudy
