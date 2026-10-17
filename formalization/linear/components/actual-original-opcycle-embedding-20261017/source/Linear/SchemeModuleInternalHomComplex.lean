module
public import Linear.SchemeModuleHomPrecompose
public import Mathlib.Algebra.Homology.Opposite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- ACTUAL internal Hom of ORIGINAL module sheaves, as an actual
contravariant functor in its original source. Reuse actual local Hom
sections and their proved original precomposition; no new Hom model. -/
def schemeModuleInternalHomFunctor (X : Scheme.{u}) (N : X.Modules) :
    X.Modulesᵒᵖ ⥤ X.Modules where
  obj M := schemeModuleHomModuleSheaf M.unop N
  map f := schemeModuleHomPrecompose f.unop
  map_id M := schemeModuleHomPrecompose_id
  map_comp f g := schemeModuleHomPrecompose_comp g.unop f.unop

instance schemeModuleInternalHomFunctor_additive (X : Scheme.{u}) (N : X.Modules) :
    (schemeModuleInternalHomFunctor X N).Additive where
  map_add := fun {A B f g} => schemeModuleHomPrecompose_add f.unop g.unop

/-- Apply the ACTUAL internal-Hom functor to the opposite of the SAME
original chain complex. This is a native CochainComplex of module sheaves;
it does not identify derived SHEAF Ext or global sheaf cohomology. -/
def schemeModuleInternalHomCochainComplex {X : Scheme.{u}} (N : X.Modules)
    (K : ChainComplex X.Modules ℕ) : CochainComplex X.Modules ℕ :=
  ((schemeModuleInternalHomFunctor X N).mapHomologicalComplex (ComplexShape.up ℕ)).obj K.op

theorem schemeModuleInternalHomCochainComplex_X {X : Scheme.{u}} (N : X.Modules)
    (K : ChainComplex X.Modules ℕ) (j : ℕ) :
    (schemeModuleInternalHomCochainComplex N K).X j =
      schemeModuleHomModuleSheaf (K.X j) N := rfl

/-- The ACTUAL cochain differential is precomposition by the SAME
original chain differential, with its original direction retained. -/
theorem schemeModuleInternalHomCochainComplex_d {X : Scheme.{u}} (N : X.Modules)
    (K : ChainComplex X.Modules ℕ) (i j : ℕ) :
    (schemeModuleInternalHomCochainComplex N K).d i j =
      schemeModuleHomPrecompose (K.d j i) := rfl

end LinearStudy
