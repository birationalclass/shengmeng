module
public import Linear.OrderedFormalCechComplex
public import Mathlib.Algebra.Homology.Functor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u v w v' w'
variable {X : Scheme.{u}} {A : Type w} [Category.{v} A] [Preadditive A]
variable {B : Type w'} [Category.{v'} B] [Preadditive B]
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
/-- An actual coefficient isomorphism gives the SAME ordered complex isomorphism,
with every original differential and sign retained. -/
def orderedFormalCechComplexIso {F G : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ A} (a : F ≅ G) :
    orderedFormalCechComplex F U ≅ orderedFormalCechComplex G U := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => a.app (op (orderedCechFormalObject U n))) ?_
  intro i j hij
  have hj : i+1=j := hij
  subst j
  simp only [orderedFormalCechComplex_d,orderedFormalCechDifferential,sum_comp,comp_sum,
    zsmul_comp,comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
    (a.hom.naturality (orderedCechFace U i k).op).symm
/-- Additive coefficient functors commute with the SAME ordered differential complex. -/
def orderedFormalCechWhiskeringIso (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ A)
    (H : A ⥤ B) [H.Additive] :
    (H.mapHomologicalComplex (.up ℕ)).obj (orderedFormalCechComplex F U) ≅
      orderedFormalCechComplex (F ⋙ H) U := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j hij
  have hj : i+1=j := hij
  subst j
  change 𝟙 _ ≫ (orderedFormalCechComplex (F ⋙ H) U).d i (i+1) =
    H.map ((orderedFormalCechComplex F U).d i (i+1)) ≫ 𝟙 _
  simp only [Category.comp_id,Category.id_comp,orderedFormalCechComplex_d,
    orderedFormalCechDifferential,H.map_sum,H.map_zsmul]
  rfl
end LinearStudy
