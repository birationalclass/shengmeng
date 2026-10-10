module
public import Linear.SchemeModuleHomModuleSections
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Compatible ACTUAL local O-module morphisms glue uniquely on the original
cover. The condition compares the original Over restriction functors,
including mathlib's actual comparison isomorphisms. -/
theorem schemeModuleHom_existsUnique_gluing {ι : Type*}
    (U : ι → X.Opens) (V : X.Opens) (iUV : ∀ i, U i ⟶ V)
    (hcover : V ≤ iSup U) (f : ∀ i, M.over (U i) ⟶ N.over (U i))
    (h : ∀ i j, schemeModuleHomRestrict M N (infLELeft (U i) (U j)) (f i) =
      schemeModuleHomRestrict M N (infLERight (U i) (U j)) (f j)) :
    ∃! g : M.over V ⟶ N.over V,
      ∀ i, schemeModuleHomRestrict M N (iUV i) g = f i := by
  let H := schemeModuleHomSheaf M N
  let sf := fun i => schemeModuleHomOverEquiv M N (U i) (f i)
  have hc : TopCat.Presheaf.IsCompatible H.obj U sf := by
    intro i j
    change (schemeModuleHomPresheaf M N).map (infLELeft (U i) (U j)).op (sf i) =
      (schemeModuleHomPresheaf M N).map (infLERight (U i) (U j)).op (sf j)
    rw [← schemeModuleHomOverEquiv_restrict, ← schemeModuleHomOverEquiv_restrict, h i j]
  obtain ⟨s,hs,hu⟩ := H.existsUnique_gluing' U V iUV hcover sf hc
  refine ⟨(schemeModuleHomOverEquiv M N V).symm s, ?_, ?_⟩
  · intro i
    apply (schemeModuleHomOverEquiv M N (U i)).injective
    rw [schemeModuleHomOverEquiv_restrict, Equiv.apply_symm_apply]
    exact hs i
  · intro g hg
    apply (schemeModuleHomOverEquiv M N V).injective
    rw [Equiv.apply_symm_apply]
    apply hu
    intro i
    change (schemeModuleHomPresheaf M N).map (iUV i).op
      (schemeModuleHomOverEquiv M N V g) = sf i
    rw [← schemeModuleHomOverEquiv_restrict, hg i]

end LinearStudy
