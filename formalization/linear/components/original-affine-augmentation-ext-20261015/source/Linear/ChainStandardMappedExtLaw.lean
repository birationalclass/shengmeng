module
public import Linear.ChainTopExtExactFunctorMappedChain
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]

/-- An explicit STATEMENT of the actual mapped-chain Ext equality.
Standard Ext and derived categories and mapped quasiiso are constructed.
The named proposition is not itself a proof. -/
def originalChainStandardMappedExtLaw
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) : Prop :=
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := HasExt.standard B
  letI := HasDerivedCategory.standard B
  letI := hAlpha
  letI := mappedOriginalChainAugmentation_quasiIso F C alpha
  (originalChainTopExtClass C r alpha a ha).mapExactFunctor F =
    originalChainTopExtClass ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) r
      (mappedOriginalChainAugmentation F C alpha) (F.map a)
      (by change F.map (C.d _ _) ≫ F.map a = 0; rw [← F.map_comp,ha,F.map_zero])

/-- Prove that exact native functor action equals the actual SAME mapped
chain resolution's Ext class. No Ext comparison is supplied as a premise. -/
theorem originalChainStandardMappedExtLaw_proof
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    originalChainStandardMappedExtLaw F C r alpha hAlpha a ha := by
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := HasExt.standard B
  letI := HasDerivedCategory.standard B
  letI := hAlpha
  exact originalChainTopExtClass_mapExactFunctor_eq_mappedChain F C r alpha a ha

end LinearStudy
