module
public import Linear.ChainExplicitStandardTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe v u
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Coefficient pushforward of the constructed roof is represented by
its SAME top functional followed by g, with no chosen class as input. -/
theorem originalChainExplicitStandardTopExtClass_comp_mk₀
    (C : ChainComplex A ℕ) {E M N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) (g : M ⟶ N) :
    letI := HasExt.standard A
    (originalChainExplicitStandardTopExtClass C r alpha hAlpha a ha).comp
        (Ext.mk₀ g) (add_zero _) =
      originalChainExplicitStandardTopExtClass C r alpha hAlpha (a ≫ g)
        (by simp [reassoc_of% ha]) := by
  letI := hAlpha
  exact originalChainStandardTopExtClassPushProof C r alpha a ha g

/-- Actual proof of naturality for ALL coefficient sheaves/morphisms,
prepared before the concrete original geometric specialization. -/
def originalChainExplicitStandardTopExtClassAllPushProof
    (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :=
  fun (N : A) (g : M ⟶ N) =>
    originalChainExplicitStandardTopExtClass_comp_mk₀ C r alpha hAlpha a ha g

end LinearStudy
