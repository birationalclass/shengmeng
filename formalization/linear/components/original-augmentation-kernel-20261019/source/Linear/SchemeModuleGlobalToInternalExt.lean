module
public import Linear.SchemeModuleInjectiveInternalHomCycles
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Group.Subgroup.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {N : X.Modules} (I : InjectiveResolution N) (P : X.Modules)

/-- SAME injective cocycle as an ACTUAL derived SHEAF Ext global section,
using the native comparison for this SAME injective resolution. -/
def schemeModuleInjectiveCocycleToInternalExt (q : ℕ) :
    injectiveCocycleGroup I P q →+
      (SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleInternalExt P N q) where
  toFun f := schemeModuleInjectiveInternalHomClassMap I P q f ≫
    (schemeModuleInternalExtInjectiveResolutionIso P N q I).inv
  map_zero' := by simp
  map_add' f g := by simp [Preadditive.add_comp]

/-- Construct an ACTUAL positive global-to-local Ext map via an actual
chosen coefficient injective resolution. Descend by the PROVED native
cocycle presentation and PROVED boundary vanishing. No desired descent
map or kernel condition is a premise. Resolution independence and SAME
Koszul comparison are separate obligations. -/
def schemeModuleGlobalToInternalExtViaResolution (n : ℕ) :
    Ext.{u} P N (n+1) →+
      (SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleInternalExt P N (n+1)) :=
  (injectiveCocycleExtMap I P (n+1)).liftOfSurjective
    (injectiveCocycleExtMap_surjective I P (n+1))
    ⟨schemeModuleInjectiveCocycleToInternalExt I P (n+1),by
      intro f hf
      obtain ⟨g,hg⟩ := (injectiveCocycleExtMap_succ_eq_zero_iff I P n f).mp hf
      change schemeModuleInjectiveInternalHomClassMap I P (n+1) f ≫ _ = 0
      rw [schemeModuleInjectiveInternalHomClassMap_boundary_zero I P n f g hg,zero_comp]⟩

/-- The constructed map sends SAME native extMk to SAME actual sheaf
cycle class;the representative formula is proved after quotient descent. -/
theorem schemeModuleGlobalToInternalExtViaResolution_extMk (n : ℕ)
    (f : P ⟶ I.cocomplex.X (n+1))
    (hf : f ≫ I.cocomplex.d (n+1) (n+1+1) = 0) :
    schemeModuleGlobalToInternalExtViaResolution I P n
        (I.extMk f (n+1+1) rfl hf) =
      schemeModuleInjectiveCocycleToInternalExt I P (n+1) ⟨f,hf⟩ := by
  change schemeModuleGlobalToInternalExtViaResolution I P n
    (injectiveCocycleExtMap I P (n+1) ⟨f,hf⟩) = _
  simp only [schemeModuleGlobalToInternalExtViaResolution,AddMonoidHom.liftOfSurjective,
    AddMonoidHom.liftOfRightInverse_comp_apply]

/-- The same map with values in ACTUAL global sections over the whole
original space,evaluating its structure-unit morphism at 1. -/
def schemeModuleGlobalToInternalExtSectionsViaResolution (n : ℕ) :
    Ext.{u} P N (n+1) →+ Γ(schemeModuleInternalExt P N (n+1),⊤) where
  toFun e := Scheme.Modules.Hom.app (X := X)
    (schemeModuleGlobalToInternalExtViaResolution I P n e) ⊤ (1 : Γ(X,⊤))
  map_zero' := by rw [map_zero]; rfl
  map_add' e e' := by rw [map_add]; rfl

end LinearStudy
