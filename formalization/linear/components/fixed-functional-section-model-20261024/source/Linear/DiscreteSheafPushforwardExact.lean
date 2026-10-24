module
public import Linear.DiscreteSheafSectionsExact
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

/-- Native abelian-sheaf inverse image preserves finite limits,using
representable flatness of ORIGINAL preimage on open sets. -/
theorem actualAbelianSheaf_pullback_preservesFiniteLimits
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  delta TopCat.Sheaf.pullback
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map f) AddCommGrpCat.{u} _ _

/-- Actual abelian-sheaf inverse image is additive,using its native
preservation of finite limits. No ringed-module pullback substituted. -/
theorem actualAbelianSheaf_pullback_additive
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).Additive := by
  letI := actualAbelianSheaf_pullback_preservesFiniteLimits f
  exact Functor.additive_of_preserves_binary_products _

/-- Actual abelian-sheaf direct image is additive by native right-adjoint
finite-limit preservation. -/
theorem actualAbelianSheaf_pushforward_additive
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- ACTUAL direct image from a discrete source preserves epis,using the
proved surjectivity on each ORIGINAL inverse-image open section group. -/
theorem discreteAbelianSheaf_pushforward_preservesEpimorphisms
    {X Y : TopCat.{u}} [DiscreteTopology X] (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesEpimorphisms where
  preserves g _ := by
    apply (TopCat.Sheaf.forget AddCommGrpCat.{u} Y).epi_of_epi_map
    letI : ∀ U,Epi (((TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g)).app U) := by
      intro U
      change Epi (g.hom.app (op ((Opens.map f).obj U.unop)))
      exact discreteAbelianSheaf_sections_epi g _
    exact NatTrans.epi_of_epi_app _

/-- ACTUAL direct image from a discrete source is exact. It is left exact
as the native right adjoint and preserves epis by the proved section maps;
apply native short-exact/finite-colimit equivalence. -/
theorem discreteAbelianSheaf_pushforward_preservesFiniteColimits
    {X Y : TopCat.{u}} [DiscreteTopology X] (f : X ⟶ Y) :
    PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) := by
  let G := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f
  letI : G.Additive := actualAbelianSheaf_pushforward_additive f
  letI : PreservesFiniteLimits G := by dsimp [G]; infer_instance
  letI : G.PreservesEpimorphisms := discreteAbelianSheaf_pushforward_preservesEpimorphisms f
  apply ((Functor.preservesFiniteColimits_tfae G).out 1 4 rfl rfl).mp
  intro S hS
  letI := hS.epi_g
  exact ⟨(((Functor.preservesFiniteLimits_tfae G).out 4 1 rfl rfl).mp (inferInstance : PreservesFiniteLimits G) S hS).1,
    inferInstance⟩

end LinearStudy
