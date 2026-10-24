module
public import Linear.SchemeModuleExtClassActualSectionBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
variable {X : Scheme.{u}} {E M : X.Modules} {r : ℕ}
/-- The SAME actual section boundary is additive. This is an object
construction,not a proof of geometric Serre or proper duality. -/
def schemeModuleExtClassActualSectionBoundaryAddHom (epsilon : Ext.{u} E M r) :
    Γ(E,⊤) →+ schemeModuleActualCohomology X M r where
  toFun := schemeModuleExtClassActualSectionBoundary epsilon
  map_zero' := by
    simp only [schemeModuleExtClassActualSectionBoundary,map_zero,Ext.mk₀_zero,Ext.zero_comp]
  map_add' s t := by
    simp only [schemeModuleExtClassActualSectionBoundary,map_add,Ext.mk₀_add,Ext.add_comp]
/-- Actual additive boundary of the SAME original Koszul/chain roof,
with the SAME top identification and actual original augmentation. -/
def schemeModuleOriginalActualSectionBoundary
    (C : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (C.X (r+1))) (phi : C.X r ≅ M) :
    Γ(E,⊤) →+ schemeModuleActualCohomology X M r :=
  schemeModuleExtClassActualSectionBoundaryAddHom
    (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha phi.hom (hAbove.eq_of_src _ _))
/-- Exact actual section sequence: the boundary is ONTO native H and
its kernel is the image of the ACTUAL original augmentation on sections.
This statement contains no vanishing or exactness assumption. -/
def schemeModuleOriginalActualSectionExactStatement
    (C : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (C.X (r+1))) (phi : C.X r ≅ M) : Prop :=
  Function.Surjective (schemeModuleOriginalActualSectionBoundary C r alpha hAlpha hAbove phi) ∧
    ∀ s : Γ(E,⊤),schemeModuleOriginalActualSectionBoundary C r alpha hAlpha hAbove phi s = 0 ↔
      ∃ z : Γ(C.X 0,⊤),(alpha.f 0).app ⊤ z = s
/-- Prove the actual-section exact sequence from the previously proved
SAME original unit-source covariant roof exactness. No replacement
boundary or section restriction is introduced. -/
theorem schemeModuleOriginalActualSectionExactStatement_of_unit
    (C : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (C.X (r+1))) (phi : C.X r ≅ M)
    (h : schemeModuleOriginalCovariantAtSourceStatement C r alpha hAlpha hAbove phi
      (SheafOfModules.unit X.ringCatSheaf)) :
    schemeModuleOriginalActualSectionExactStatement C r alpha hAlpha hAbove phi := by
  exact ⟨schemeModuleExtClassActualSectionBoundary_surjective _ h.1,
    fun s => schemeModuleExtClassActualSectionBoundary_kernel (alpha.f 0) _ h.2 s⟩
end LinearStudy
