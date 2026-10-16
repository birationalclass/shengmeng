module
public import Linear.SchemeModuleInternalExtSourceMap
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The SAME actual coefficient-complex source map preserves addition. -/
theorem schemeModuleHomCoefficientComplexMap_add {A B : X.Modules} (f g : A ⟶ B)
    (K : CochainComplex X.Modules ℕ) :
    schemeModuleHomCoefficientComplexMap (f+g) K =
      schemeModuleHomCoefficientComplexMap f K + schemeModuleHomCoefficientComplexMap g K := by
  ext j : 1
  exact schemeModuleHomPrecompose_add (N := K.X j) f g

/-- ACTUAL derived SHEAF Ext source maps preserve addition,using the SAME
coefficient resolution and SAME actual original precomposition maps. -/
theorem schemeModuleInternalExtSourceMap_add {A B : X.Modules} (f g : A ⟶ B)
    (N : X.Modules) (q : ℕ) :
    schemeModuleInternalExtSourceMap (f+g) N q =
      schemeModuleInternalExtSourceMap f N q + schemeModuleInternalExtSourceMap g N q := by
  let I : InjectiveResolution N := injectiveResolution N
  rw [schemeModuleInternalExtSourceMap_resolution (f+g) N q I,
    schemeModuleHomCoefficientComplexMap_add,HomologicalComplex.homologyMap_add]
  dsimp only [schemeModuleHomCoefficientComplex]
  simp only [Preadditive.comp_add,Preadditive.add_comp]
  rw [← schemeModuleInternalExtSourceMap_resolution f N q I,
    ← schemeModuleInternalExtSourceMap_resolution g N q I]

/-- ACTUAL derived SHEAF Ext,contravariant in its SAME source sheaf. -/
def schemeModuleInternalExtSourceFunctor (X : Scheme.{u}) (N : X.Modules) (q : ℕ) :
    X.Modulesᵒᵖ ⥤ X.Modules where
  obj P := schemeModuleInternalExt P.unop N q
  map f := schemeModuleInternalExtSourceMap f.unop N q
  map_id P := schemeModuleInternalExtSourceMap_id P.unop N q
  map_comp f g := schemeModuleInternalExtSourceMap_comp g.unop f.unop N q

/-- Additivity of the ACTUAL derived SHEAF Ext source functor. -/
theorem schemeModuleInternalExtSourceFunctor_additive (X : Scheme.{u}) (N : X.Modules)
    (q : ℕ) : (schemeModuleInternalExtSourceFunctor X N q).Additive where
  map_add := fun {A B f g} => schemeModuleInternalExtSourceMap_add f.unop g.unop N q

end LinearStudy
