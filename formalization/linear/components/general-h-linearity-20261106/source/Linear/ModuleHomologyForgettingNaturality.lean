module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u
/-- Native forgetting-of-scalars homology comparison is natural in the
ORIGINAL complex map,by mathlib's original short-complex naturality. -/
theorem moduleHomologyForgettingIso_coefficient_naturality
    {R : Type u} [Ring R] {ι : Type} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) (n : ι) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (HomologicalComplex.homologyMap f n) ≫
        ((L.sc n).mapHomologyIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv =
      ((K.sc n).mapHomologyIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv ≫
        HomologicalComplex.homologyMap
          (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex c).map f) n := by
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) c n).map f)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
end LinearStudy
