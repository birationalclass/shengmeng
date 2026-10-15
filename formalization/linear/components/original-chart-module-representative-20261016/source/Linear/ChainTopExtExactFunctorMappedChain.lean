module
public import Linear.OriginalChainMappedExtComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u v' u' wA wB dA dB
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable [HasExt.{wA} A] [HasDerivedCategory.{dA} A]
variable [HasExt.{wB} B] [HasDerivedCategory.{dB} B]

/-- Native exact-functor action on the SAME original chain-resolution
class equals the class of its ACTUAL mapped CHAIN complex, original
mapped augmentation and SAME mapped top functional. No desired class
comparison is assumed. -/
theorem originalChainTopExtClass_mapExactFunctor_eq_mappedChain
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    letI := mappedOriginalChainAugmentation_quasiIso F C alpha
    (originalChainTopExtClass C r alpha a ha).mapExactFunctor F =
      originalChainTopExtClass ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) r
        (mappedOriginalChainAugmentation F C alpha) (F.map a)
        (by change F.map (C.d _ _) ≫ F.map a = 0; rw [← F.map_comp,ha,F.map_zero]) := by
  rw [originalChainTopExtClass_mapExactFunctor]
  exact originalChainMappedTopExtClass_eq_mappedChain F C r alpha a ha

end LinearStudy
