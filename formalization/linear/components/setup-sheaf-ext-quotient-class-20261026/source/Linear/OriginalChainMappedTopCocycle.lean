module
public import Linear.MappedCochainTopCocycle
public import Linear.OriginalChainMappedAugmentationComparison
public import Linear.ChainTopExtExactFunctorCompatibility
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive]

/-- Compare the SAME original top cocycle after the constructed actual
chain/cochain comparison. Neither a replacement cocycle nor a desired
class equality is supplied. -/
theorem mappedOriginalChainTopCocycle
    (C : ChainComplex A ℕ) {M : A} (r : ℕ)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    mappedCochainResolutionCocycle F (originalChainAsCochain C) r
        (originalChainTopShiftedCocycle C r a ha) =
      (additiveFunctorOriginalChainCochainIso F C).hom ≫
        originalChainTopShiftedCocycle ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) r
          (F.map a) (by change F.map (C.d _ _) ≫ F.map a = 0; rw [← F.map_comp,ha,F.map_zero]) := by
  simp only [originalChainTopShiftedCocycle]
  rw [mappedCochainResolutionTopCocycle]
  rw [← Cocycle.equivHomShift_symm_precomp,← Cocycle.toSingleMk_precomp]
  congr 2
  simp only [Functor.map_comp,← Category.assoc]
  exact congrArg (fun z => z ≫ F.map a)
    (additiveFunctorExtendXIso_comp_XIso F C
      (ComplexShape.embeddingDownNat.r_eq_some (show ComplexShape.embeddingDownNat.f r = -(r:ℤ) from rfl))).symm

end LinearStudy