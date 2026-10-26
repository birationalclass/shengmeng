module
public import Linear.SchemeModuleInjectiveInternalHomSourceNaturality
public import Linear.SchemeModuleGlobalToInternalExtCocycle
public import Mathlib.CategoryTheory.CommSq
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {N : X.Modules} (I : InjectiveResolution N)

/-- The SAME injective cocycle maps source-naturally to actual derived SHEAF Ext. -/
theorem schemeModuleInjectiveCocycleToInternalExt_sourceNaturality
    {P Q : X.Modules} (g : P ⟶ Q) (q : ℕ) (f : injectiveCocycleGroup I Q q) :
    schemeModuleInjectiveCocycleToInternalExt I P q (injectiveCocyclePrecompose I g q f) =
      schemeModuleInjectiveCocycleToInternalExt I Q q f ≫
        schemeModuleInternalExtSourceMap g N q := by
  let a := schemeModuleInternalExtInjectiveResolutionIso Q N q I
  let b := schemeModuleInternalExtInjectiveResolutionIso P N q I
  have hs : CommSq (schemeModuleInternalExtSourceMap g N q) a.hom b.hom
      (HomologicalComplex.homologyMap (schemeModuleHomCoefficientComplexMap g I.cocomplex) q) :=
    ⟨schemeModuleInternalExtSourceMap_resolution_square g N q I⟩
  have hi := (CommSq.vert_inv (g := a) (h := b) hs).w
  change schemeModuleInjectiveInternalHomClassMap I P q _ ≫ b.inv =
    (schemeModuleInjectiveInternalHomClassMap I Q q f ≫ a.inv) ≫ _
  rw [schemeModuleInjectiveInternalHomClassMap_sourceNaturality]
  simp only [Category.assoc]
  rw [hi]

end LinearStudy
