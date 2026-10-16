module
public import Linear.OriginalChainIteratedSourceBoundary
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
attribute [local instance] originalChainAugmentationAsCochain_quasiIso
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Statement of SAME original native iterated-source equality,with standard
Ext and derived prerequisites constructed. This definition is NOT a proof. -/
def originalChainStandardSourceBoundaryStatement
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) : Prop :=
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := hAlpha
  cochainOpcycleIteratedBoundary (originalChainAsCochain C) r
    (originalChainAugmentationAsCochain C alpha) r le_rfl
    (Ext.mk₀ (originalChainTopOpcycleFunctional C r a ha)) =
    (Ext.mk₀ (cochainSourceTerminalMap r
      (cochainAugmentationOpcycle (originalChainAugmentationAsCochain C alpha)))).comp
      (originalChainTopExtClass C r alpha a ha) (zero_add r)

/-- ACTUAL proof for every original positive rank,using a constructed native
injective resolution. No chosen representative or class-identity condition. -/
theorem originalChainStandardSourceBoundaryStatement_proof [EnoughInjectives A]
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    originalChainStandardSourceBoundaryStatement C r alpha hAlpha a ha := by
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := hAlpha
  exact originalChainTopExtClass_iteratedSourceBoundary C r hr alpha a ha (InjectiveResolution.of N)

end LinearStudy
