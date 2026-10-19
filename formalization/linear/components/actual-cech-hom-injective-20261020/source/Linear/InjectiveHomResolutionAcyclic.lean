module
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.QuasiIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace LinearStudy
/-- ANY actual native chain resolution of Z gives positive exact Hom cochains into
an injective object,in an arbitrary abelian category. This does not assume source projectivity. -/
theorem injectiveHomOppositeOfResolution_exactAt
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : ChainComplex A ℕ) (Z : A) (f : K ⟶ (ChainComplex.single₀ A).obj Z)
    [QuasiIso f] (F : A) [Injective F] (n : ℕ) :
    ((preadditiveYoneda.obj F).mapHomologicalComplex (.up ℕ)).obj K.op |>.ExactAt (n+1) := by
  let H := preadditiveYoneda.obj F
  letI : H.PreservesHomology := by
    dsimp [H,preadditiveYoneda]
    infer_instance
  let fop := (HomologicalComplex.opFunctor A (.down ℕ)).map f.op
  letI : QuasiIso fop := inferInstance
  let q := (H.mapHomologicalComplex (.up ℕ)).map fop
  letI : QuasiIso q := inferInstance
  have hz : IsZero (((ChainComplex.single₀ A).obj Z).X (n+1)) :=
    HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 Z (n+1) (by omega)
  have hs : ((H.mapHomologicalComplex (.up ℕ)).obj
      (((ChainComplex.single₀ A).obj Z).op)).ExactAt (n+1) :=
    HomologicalComplex.ExactAt.of_isZero (H.map_isZero hz.op)
  exact (exactAt_iff_of_quasiIsoAt q (n+1)).mp hs
end LinearStudy
