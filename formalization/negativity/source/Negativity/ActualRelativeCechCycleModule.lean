module

public import Negativity.ActualRelativeCechGradedAction
public import Mathlib.Algebra.Module.GradedModule
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[instance_reducible] def actualRelativeCechOneModule {X Y : Scheme.{u}}
    (f : X ⟶ Y) {ι : Type v} (U : ι → X.Opens) :
    Module Γ(Y, ⊤) (actualCechOne X U) := by
  letI (j k : ι) : Module Γ(Y, ⊤) Γ(X, U j ⊓ U k) :=
    Module.compHom Γ(X, U j ⊓ U k)
      ((actualSectionRestriction X (U := U j ⊓ U k) (V := ⊤) le_top).comp f.appTop.hom)
  exact inferInstanceAs (Module Γ(Y, ⊤) (∀ j k, Γ(X, U j ⊓ U k)))

def actualRelativeCechCycleModule {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.Opens) (n : ℕ) :
    letI := actualRelativeCechOneModule f U
    Submodule Γ(Y, ⊤) (actualCechOne X U) := by
  letI := actualRelativeCechOneModule f U
  exact {
    __ := (actualClosedCechCocycles ((I ^ n).comap f).subschemeι U).toAddSubmonoid
    smul_mem' := by
      intro r a ha
      change actualCechScaleOne X U (f.appTop r) a ∈
        actualClosedCechCocycles ((I ^ n).comap f).subschemeι U
      exact (actualClosedCechScaleCycle ((I ^ n).comap f).subschemeι U
        (f.appTop r) ⟨a, ha⟩).2 }

@[instance_reducible] def actualRelativeCechCycleGradedSMul {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ j k, IsAffineOpen (U j ⊓ U k)) :
    letI := actualRelativeCechOneModule f U
    SetLike.GradedSMul (fun n : ℕ => (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n)
      (actualRelativeCechCycleModule f I U) := by
  letI := actualRelativeCechOneModule f U
  exact ⟨by
    intro m n r a hr ha
    exact actual_relative_cech_graded_cocycle_multiplication
      f I U hU m n r hr ⟨a, ha⟩⟩

/-- Final theorem: the direct sum of actual ideal Cech cocycles carries
the genuine module structure over the direct-sum Rees ring. The action
uses actual pullback of base functions and actual restrictions. The
graded multiplication and all module axioms are constructed, without a
finite-generation input or claim. -/
theorem actual_relative_cech_cycles_rees_module
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ j k, IsAffineOpen (U j ⊓ U k)) :
    Nonempty (Module (⨁ n : ℕ, ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (⨁ n : ℕ, actualRelativeCechCycleModule f I U n)) := by
  letI := actualRelativeCechOneModule f U
  letI := actualRelativeCechCycleGradedSMul f I U hU
  exact ⟨inferInstance⟩

end
end Negativity
