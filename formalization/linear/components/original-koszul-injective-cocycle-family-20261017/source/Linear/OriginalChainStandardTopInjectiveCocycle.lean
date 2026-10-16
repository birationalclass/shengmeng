module
public import Linear.OriginalChainTopInjectiveCocycle
public import Linear.ChainExplicitStandardTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- ACTUAL proof value of the original all-degree representative and source
homotopy,with native Ext and derived prerequisites constructed at the boundary. -/
def originalChainExplicitStandardTopInjectiveCocycleProof
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) (I : InjectiveResolution N) :=
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := hAlpha
  originalChainTopInjectiveCocycle_exists C r alpha a ha I

end LinearStudy
