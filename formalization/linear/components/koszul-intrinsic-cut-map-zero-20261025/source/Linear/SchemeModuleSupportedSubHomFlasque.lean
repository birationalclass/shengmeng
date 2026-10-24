module
public import Linear.ClosedDiscreteSupportSheafFlasque
public import Linear.DiscreteClosedMapSupportFlasque
public import Linear.SchemeModuleHomZeroSourceSupport
public import Linear.SchemeModuleSupportedRestrictionUnit
public import Linear.SchemeModuleFiniteSupportCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Every ACTUAL subobject of Hom(P,N) is flasque as an actual abelian sheaf when P vanishes off a closed discrete support. Coefficient N is arbitrary; cycles and boundaries are included by their original mono maps. -/
theorem schemeModuleSubHom_supportedFlasque {X : Scheme.{u}} (S : Set X)
    (hclosed : ∀ U : X.Opens, IsClosed (S ∩ (U : Set X)))
    (P N M : X.Modules) (g : M ⟶ schemeModuleHomModuleSheaf P N) [Mono g]
    (hP : ∀ U : X.Opens, Disjoint (U : Set X) S → IsZero (P.restrict U.ι)) :
    TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj M) := by
  refine closedDiscreteSupportAbelianSheaf_isFlasque S hclosed
    ((schemeModuleToActualAbelianSheaf X).obj M) ?_
  intro U hU
  let V : X.Opens := U
  have hz := schemeModuleSubHom_open_isZero_of_source V.ι P N M g (hP V hU)
  have hs := schemeModule_sections_isZero_of_openRestriction V.ι M hz V
    (le_of_eq V.ι_image_top.symm)
  exact AddCommGrpCat.subsingleton_of_isZero hs
/-- The actual closed map from a discrete source DERIVES the closed-slice condition. The remaining source support condition will be derived from actual direct image. -/
theorem schemeModuleSubHom_closedDiscreteFlasque {D X : Scheme.{u}}
    [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (P N M : X.Modules) (g : M ⟶ schemeModuleHomModuleSheaf P N) [Mono g]
    (hP : ∀ U : X.Opens, Disjoint (U : Set X) (Set.range f) → IsZero (P.restrict U.ι)) :
    TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj M) :=
  schemeModuleSubHom_supportedFlasque (Set.range f)
    (discreteClosedMap_range_inter_open_isClosed f.base hf) P N M g hP
end LinearStudy
