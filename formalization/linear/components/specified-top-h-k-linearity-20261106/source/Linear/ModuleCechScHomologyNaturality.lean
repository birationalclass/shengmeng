module
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HomologicalComplex
open CategoryTheory
universe u v
variable {R : Type u} [Ring R] {ι : Type} {c : ComplexShape ι}
    {A B : HomologicalComplex (ModuleCat.{v} R) c}

/-- Reuse mathlib's natural short-complex comparison and homology functor.
This verifies the comparison square for the original cochain morphism. -/
theorem moduleCatHomologyIsoSc'_naturality (φ : A ⟶ B) (i j k : ι)
    (hi : c.prev j = i) (hk : c.next j = k) :
    homologyMap φ j ≫ (B.homologyIsoSc' i j k hi hk).hom =
    (A.homologyIsoSc' i j k hi hk).hom ≫
      ShortComplex.homologyMap ((shortComplexFunctor' (ModuleCat.{v} R) c i j k).map φ) := by
  change ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat.{v} R) c j).map φ) ≫
      ShortComplex.homologyMap (B.isoSc' i j k hi hk).hom =
    ShortComplex.homologyMap (A.isoSc' i j k hi hk).hom ≫
      ShortComplex.homologyMap ((shortComplexFunctor' (ModuleCat.{v} R) c i j k).map φ)
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  exact congrArg (fun f => ShortComplex.homologyMap f)
    ((natIsoSc' (ModuleCat.{v} R) c i j k hi hk).hom.naturality φ)

end HomologicalComplex
