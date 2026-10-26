module
public import Linear.SchemeModuleInternalExtSourceMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The actual derived SHEAF Ext source sequence uses SAME original source maps. -/
def schemeModuleInternalExtSourceShortComplex (S : ShortComplex X.Modules)
    (N : X.Modules) (q : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (schemeModuleInternalExtSourceMap S.g N q)
    (schemeModuleInternalExtSourceMap S.f N q) (by
      rw [← schemeModuleInternalExtSourceMap_comp,S.zero,
        schemeModuleInternalExtSourceMap_zero])

/-- Compare SAME actual source maps with ANY actual coefficient injective
resolution. No exactness of derived SHEAF Ext is assumed. -/
def schemeModuleInternalExtSourceResolutionIso (S : ShortComplex X.Modules)
    (N : X.Modules) (q : ℕ) (I : InjectiveResolution N) :
    schemeModuleInternalExtSourceShortComplex S N q ≅
      (schemeModuleHomSourceShortComplex S I.cocomplex).map
        (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℕ) q) :=
  ShortComplex.isoMk
    (schemeModuleInternalExtInjectiveResolutionIso S.X₃ N q I)
    (schemeModuleInternalExtInjectiveResolutionIso S.X₂ N q I)
    (schemeModuleInternalExtInjectiveResolutionIso S.X₁ N q I)
    (schemeModuleInternalExtSourceMap_resolution_square S.g N q I).symm
    (schemeModuleInternalExtSourceMap_resolution_square S.f N q I).symm

/-- Exactness in the source variable for actual derived SHEAF Ext follows
from the PROVED short exactness of actual internal-Hom complexes. -/
theorem schemeModuleInternalExtSourceShortComplex_exact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (N : X.Modules) (q : ℕ) (I : InjectiveResolution N) :
    (schemeModuleInternalExtSourceShortComplex S N q).Exact := by
  apply ShortComplex.exact_of_iso (schemeModuleInternalExtSourceResolutionIso S N q I).symm
  exact (schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex).homology_exact₂ q

end LinearStudy
