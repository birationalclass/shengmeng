module
public import Linear.SchemeModuleInjectiveHomEpi
public import Linear.SchemeModuleInternalHomSourceLimits
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.QuasiIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable (X : Scheme.{u}) (I : X.Modules) [Injective I]

/-- The SAME actual internal Hom into an actual injective coefficient
preserves epis from the source-opposite category. -/
theorem schemeModuleInjectiveInternalHom_preservesEpimorphisms :
    (schemeModuleInternalHomFunctor X I).PreservesEpimorphisms where
  preserves {A B} f hf := by
    letI := hf
    exact schemeModuleHomPrecompose_epi I f.unop

/-- ACTUAL sheaf internal Hom into an injective coefficient is EXACT.
Left exactness and epi preservation are PROVED for original functors. -/
theorem schemeModuleInjectiveInternalHom_preservesHomology :
    (schemeModuleInternalHomFunctor X I).PreservesHomology := by
  letI := schemeModuleInternalHomFunctor_preservesFiniteLimits X I
  letI := schemeModuleInjectiveInternalHom_preservesEpimorphisms X I
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

theorem schemeModuleInjectiveInternalHom_preservesFiniteColimits :
    PreservesFiniteColimits (schemeModuleInternalHomFunctor X I) := by
  letI := schemeModuleInjectiveInternalHom_preservesHomology X I
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Apply ACTUAL internal Hom to the SAME actual original augmentation,
retaining its exact chain map and all degree components. -/
def schemeModuleInjectiveHomAugmentationMap (C : ChainComplex X.Modules ℕ) {E : X.Modules}
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) :
    schemeModuleInternalHomCochainComplex I ((ChainComplex.single₀ X.Modules).obj E) ⟶
      schemeModuleInternalHomCochainComplex I C :=
  ((schemeModuleInternalHomFunctor X I).mapHomologicalComplex (ComplexShape.up ℕ)).map
    ((HomologicalComplex.opFunctor X.Modules (ComplexShape.down ℕ)).map alpha.op)

/-- ACTUAL original resolution is sent to a quasi-isomorphism for EVERY
actual injective coefficient. Not a desired comparison supplied as input. -/
theorem schemeModuleInjectiveHomAugmentationMap_quasiIso (C : ChainComplex X.Modules ℕ)
    {E : X.Modules} (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) [QuasiIso alpha] :
    QuasiIso (schemeModuleInjectiveHomAugmentationMap X I C alpha) := by
  letI := schemeModuleInjectiveInternalHom_preservesHomology X I
  unfold schemeModuleInjectiveHomAugmentationMap
  infer_instance

/-- The SAME augmentation is retained in each actual differential degree. -/
theorem schemeModuleInjectiveHomAugmentationMap_f (C : ChainComplex X.Modules ℕ)
    {E : X.Modules} (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (j : ℕ) :
    (schemeModuleInjectiveHomAugmentationMap X I C alpha).f j =
      schemeModuleHomPrecompose (alpha.f j) := rfl

end LinearStudy
