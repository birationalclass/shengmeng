module
public import Linear.TopCechFreeSheafHomComplex
public import Mathlib.Algebra.Homology.Opposite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
universe u v u' v'
namespace LinearStudy
/-- The native alternating Hom cochains are the actual additive functor applied
to the opposite of the SAME native alternating chain complex,including signs. -/
def alternatingHomCochainIso
    {A : Type u} [Category.{v} A] [Preadditive A]
    {B : Type u'} [Category.{v'} B] [Preadditive B]
    (S : SimplicialObject A) (H : Aᵒᵖ ⥤ B) [H.Additive] :
    (H.mapHomologicalComplex (.up ℕ)).obj
        (((alternatingFaceMapComplex A).obj S).op) ≅
      (alternatingCofaceMapComplex B).obj (S.rightOp ⋙ H) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j hij
  have hj : i+1=j := hij
  subst j
  dsimp
  simp [AlternatingFaceMapComplex.obj_d_eq,AlternatingFaceMapComplex.objD,
    alternatingCofaceMapComplex,AlternatingCofaceMapComplex.obj,AlternatingCofaceMapComplex.objD,
    op_sum,op_zsmul]
  rfl
end LinearStudy
