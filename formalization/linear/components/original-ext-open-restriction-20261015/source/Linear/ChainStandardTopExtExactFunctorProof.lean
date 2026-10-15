module
public import Linear.ChainTopExtExactFunctorCompatibility
public import Linear.ChainExplicitStandardTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]

/-- ACTUAL compatibility proof:construct standard Ext and derived-category
prerequisites before the original geometry. The quasiiso proof remains on
the SAME original source; no mapped-class comparison is an input. -/
def originalChainExplicitStandardTopExtClassMapProof
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :=
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := HasExt.standard B
  letI := HasDerivedCategory.standard B
  letI := hAlpha
  originalChainTopExtClass_mapExactFunctor F C r alpha a ha

end LinearStudy
