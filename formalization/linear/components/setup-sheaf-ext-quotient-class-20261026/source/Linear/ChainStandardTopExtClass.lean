module
public import Linear.ChainResolutionTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe v u
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Close the native universe/derived-category prerequisites GENERICALLY.
No HasExt,chosen derived category,or projectivity assumption is passed
into the actual original application. The class is the same actual roof. -/
def originalChainStandardTopExtClass (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (f : C.X r ⟶ M) (hf : C.d (r+1) r ≫ f = 0) :
    letI := HasExt.standard A
    Ext.{max u v} E M r := by
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  exact originalChainTopExtClass C r alpha f hf

/-- ACTUAL proof value of coefficient naturality with ALL native
Ext/derived-category prerequisites constructed,not assumed. -/
def originalChainStandardTopExtClassPushProof (C : ChainComplex A ℕ) {E M N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (f : C.X r ⟶ M) (hf : C.d (r+1) r ≫ f = 0) (g : M ⟶ N) :=
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  originalChainTopExtClass_comp_mk₀ C r alpha f hf g

end LinearStudy
