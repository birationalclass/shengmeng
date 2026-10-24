module
public import Linear.SchemeModuleOriginalCovariantAtSource
public import Linear.SchemeModuleGlobalExtActualHCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
variable {X : Scheme.{u}} {E M : X.Modules} {r : ℕ}
/-- The actual global-section boundary induced by the SAME global module Ext
class, transported through the calibrated native Ext/H map. A function
construction only; additivity or proper-duality transposition is not asserted. -/
def schemeModuleExtClassActualSectionBoundary (epsilon : Ext.{u} E M r) :
    Γ(E,⊤) → schemeModuleActualCohomology X M r :=
  fun s => schemeModuleGlobalExtActualHAddEquiv X M r
    ((Ext.mk₀ ((schemeModuleUnitHomGlobalSectionsAddEquiv X E).symm s)).comp
      epsilon (zero_add r))
/-- Actual unit-Hom covariant surjectivity implies actual section-to-native-H
surjectivity, using the SAME class and calibrated section identification. -/
theorem schemeModuleExtClassActualSectionBoundary_surjective
    (epsilon : Ext.{u} E M r)
    (h : ∀ x : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) M r,
      ∃ y : SheafOfModules.unit X.ringCatSheaf ⟶ E,
        (Ext.mk₀ y).comp epsilon (zero_add r) = x) :
    Function.Surjective (schemeModuleExtClassActualSectionBoundary epsilon) := by
  intro x
  obtain ⟨y,hy⟩ := h ((schemeModuleGlobalExtActualHAddEquiv X M r).symm x)
  refine ⟨schemeModuleUnitHomGlobalSectionsAddEquiv X E y,?_⟩
  dsimp only [schemeModuleExtClassActualSectionBoundary]
  rw [AddEquiv.symm_apply_apply,hy,AddEquiv.apply_symm_apply]
/-- Kernel/image transport uses the ACTUAL original augmentation on actual
sections. No replacement section map or desired kernel equality is assumed. -/
theorem schemeModuleExtClassActualSectionBoundary_kernel
    {A : X.Modules} (a : A ⟶ E) (epsilon : Ext.{u} E M r)
    (h : ∀ x : SheafOfModules.unit X.ringCatSheaf ⟶ E,
      (Ext.mk₀ x).comp epsilon (zero_add r) = 0 ↔
        ∃ z : SheafOfModules.unit X.ringCatSheaf ⟶ A,z ≫ a = x)
    (s : Γ(E,⊤)) :
    schemeModuleExtClassActualSectionBoundary epsilon s = 0 ↔
      ∃ z : Γ(A,⊤),a.app ⊤ z = s := by
  rw [schemeModuleExtClassActualSectionBoundary,map_eq_zero_iff _
    (schemeModuleGlobalExtActualHAddEquiv X M r).injective]
  rw [h]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨schemeModuleUnitHomGlobalSectionsAddEquiv X A z,?_⟩
    have H := congrArg (schemeModuleUnitHomGlobalSectionsAddEquiv X E) hz
    rw [AddEquiv.apply_symm_apply] at H
    exact H
  · rintro ⟨z,hz⟩
    refine ⟨(schemeModuleUnitHomGlobalSectionsAddEquiv X A).symm z,?_⟩
    apply (schemeModuleUnitHomGlobalSectionsAddEquiv X E).injective
    rw [AddEquiv.apply_symm_apply]
    change a.app ⊤
      (schemeModuleUnitHomGlobalSectionsAddEquiv X A
        ((schemeModuleUnitHomGlobalSectionsAddEquiv X A).symm z)) = s
    rw [AddEquiv.apply_symm_apply,hz]
end LinearStudy
