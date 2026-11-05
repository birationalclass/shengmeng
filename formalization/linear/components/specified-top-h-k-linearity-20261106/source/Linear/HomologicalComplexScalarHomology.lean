module
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u v w
variable {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Linear R C] [CategoryWithHomology C] {ι : Type} {c : ComplexShape ι}
/-- Native complex homology preserves ACTUAL scalar multiples in EVERY
degree,by the native short-complex scalar theorem. No outgoing-zero premise. -/
theorem actualHomologicalComplex_homologyMap_smul
    {K L : HomologicalComplex C c} (a : R) (f : K ⟶ L) (n : ι) :
    HomologicalComplex.homologyMap (a • f) n = a • HomologicalComplex.homologyMap f n := by
  have h : (HomologicalComplex.shortComplexFunctor C c n).map (a • f) =
      a • (HomologicalComplex.shortComplexFunctor C c n).map f := by
    apply ShortComplex.Hom.ext
    all_goals rfl
  change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor C c n).map (a • f)) = _
  rw [h,ShortComplex.homologyMap_smul]
  rfl
/-- Exact scalar multiplication on native complex homology is induced by
the original scalar identity chain map,in every degree. -/
theorem actualHomologicalComplex_homologyMap_smul_id
    (K : HomologicalComplex C c) (a : R) (n : ι) :
    HomologicalComplex.homologyMap (a • 𝟙 K) n = a • 𝟙 (K.homology n) := by
  rw [actualHomologicalComplex_homologyMap_smul,HomologicalComplex.homologyMap_id]
end LinearStudy
