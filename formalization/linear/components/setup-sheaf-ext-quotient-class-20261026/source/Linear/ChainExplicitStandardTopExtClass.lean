module
public import Linear.ChainStandardTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe v u
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The standard actual derived roof, with its augmentation quasiiso
passed explicitly at an ABSTRACT category boundary. This avoids a new
concrete source-complex conversion during instance search. -/
def originalChainExplicitStandardTopExtClass (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    letI := HasExt.standard A
    Ext.{max u v} E M r := by
  letI := hAlpha
  exact originalChainStandardTopExtClass C r alpha a ha

/-- Actual coefficient naturality for the explicit-proof constructor.
No desired Ext identity is an input. -/
def originalChainExplicitStandardTopExtClassPushProof (C : ChainComplex A ℕ)
    {E M N : A} (r : ℕ) (alpha : C ⟶ (ChainComplex.single₀ A).obj E)
    (hAlpha : QuasiIso alpha) (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0)
    (g : M ⟶ N) :=
  letI := hAlpha
  originalChainStandardTopExtClassPushProof C r alpha a ha g

end LinearStudy
