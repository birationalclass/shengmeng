module
public import Linear.OrderedFormalCechCoefficientFunctor
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u v w t
variable {R : Type t} [Semiring R] {X : Scheme.{u}}
  {A : Type w} [Category.{v} A] [Preadditive A] [CategoryTheory.Linear R A]
/-- Formal product evaluation retains the ORIGINAL scalar identity map,
proved on native product projections rather than chosen product coordinates. -/
theorem formalProductEvaluation_map_smul_id [HasProducts.{u} A]
    (T : X.Opensᵒᵖ ⥤ A) (r : R) :
    (FormalCoproduct.evalOp.{u} X.Opens A).map (r • 𝟙 T) =
      r • 𝟙 ((FormalCoproduct.evalOp.{u} X.Opens A).obj T) := by
  apply NatTrans.ext
  funext U
  change CategoryTheory.Limits.Pi.map (fun j : U.unop.I => r • 𝟙 (T.obj (op (U.unop.obj j)))) =
    r • 𝟙 (∏ᶜ fun j : U.unop.I => T.obj (op (U.unop.obj j)))
  apply Pi.hom_ext
  intro i
  rw [CategoryTheory.Limits.Pi.map_π,CategoryTheory.Linear.smul_comp,Category.id_comp,
    CategoryTheory.Linear.comp_smul,Category.comp_id]
/-- The SAME original ordered alternating complex coefficient functor
retains scalar identity maps,including all faces and signs. -/
theorem orderedFormalCechCoefficientFunctor_map_smul_id
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ A) (r : R) :
    (orderedFormalCechCoefficientFunctor U).map (r • 𝟙 F) =
      r • 𝟙 (orderedFormalCechComplex F U) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl
end LinearStudy
