module
public import Negativity.ActualCechScalars
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[instance_reducible]
def actualCechOneGlobalModule (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    Module Γ(X,⊤) (actualCechOne X U) := by
  letI (j k : ι) : Module Γ(X,⊤) Γ(X,U j ⊓ U k) :=
    Module.compHom Γ(X,U j ⊓ U k)
      (actualSectionRestriction X (U := U j ⊓ U k) le_top)
  exact inferInstanceAs (Module Γ(X,⊤) (∀ j k, Γ(X,U j ⊓ U k)))

def actualCechCycleSubmodule (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    letI := actualCechOneGlobalModule X U
    Submodule Γ(X,⊤) (actualCechOne X U) := by
  letI := actualCechOneGlobalModule X U
  exact {
    __ := (actualCechCocycles X U).toAddSubmonoid
    smul_mem' := by
      intro r a ha
      change actualCechBoundary X U (actualCechScaleOne X U r a) = 0
      funext j k l
      rw [actual_cech_boundary_scale]
      have h := congrFun (congrFun (congrFun ha j) k) l
      rw [h]
      exact mul_zero _ }

@[instance_reducible]
def actualCechCycleGlobalModule (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    Module Γ(X,⊤) (actualCechCocycles X U) := by
  letI := actualCechOneGlobalModule X U
  exact inferInstanceAs (Module Γ(X,⊤) (actualCechCycleSubmodule X U))

def actualCechBoundarySubmodule (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    letI := actualCechCycleGlobalModule X U
    Submodule Γ(X,⊤) (actualCechCocycles X U) := by
  letI := actualCechCycleGlobalModule X U
  exact {
    __ := (actualCechCoboundary X U).range.toAddSubmonoid
    smul_mem' := by
      rintro r a ⟨c, rfl⟩
      refine ⟨actualCechScaleZero X U r c, ?_⟩
      apply Subtype.ext
      exact actual_cech_difference_scale X U r c }

@[instance_reducible]
def actualCechHOneGlobalModule (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    Module Γ(X,⊤) (actualCechHOne X U) := by
  letI := actualCechCycleGlobalModule X U
  exact inferInstanceAs (Module Γ(X,⊤)
    (actualCechCocycles X U ⧸ actualCechBoundarySubmodule X U))

#print axioms actualCechHOneGlobalModule
end
end Negativity
