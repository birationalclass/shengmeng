module
public import Linear.SchemeModuleInternalHomCoefficientLimits
public import Linear.SchemeModuleInternalHomSourceLimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The SAME actual native open restriction is additive on actual maps. -/
theorem schemeModuleOverFunctor_additive (X : Scheme.{u}) (U : X.Opens) :
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).Additive where
  map_add {M N} f g := by
    apply SheafOfModules.hom_ext
    ext W x
    rfl

attribute [instance] schemeModuleOverFunctor_additive

/-- Actual restriction to an original open is EXACT: both finite-limit
and finite-colimit preservation were PROVED for the SAME native functor. -/
theorem schemeModuleOverFunctor_preservesHomology (U : X.Opens) :
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).PreservesHomology := by
  let F := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
  letI := schemeModuleOverFunctor_preservesFiniteLimits X U
  letI := schemeModuleOverFunctor_preservesFiniteColimits X U
  have h : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    ⟨inferInstance,inferInstance⟩
  change F.PreservesHomology
  exact ((Functor.exact_tfae F).out 4 3).mp h

/-- ACTUAL cohomology commutes with SAME original open restriction.
Reuse native short-complex mapHomologyIso,not a desired locality input. -/
def schemeModuleOverHomologyIso (U : X.Opens) (K : CochainComplex X.Modules ℕ)
    (q : ℕ) :
    (((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q ≅ (K.homology q).over U := by
  letI := schemeModuleOverFunctor_additive X U
  letI := schemeModuleOverFunctor_preservesHomology U
  exact (K.sc q).mapHomologyIso (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)

end LinearStudy
