module
public import Linear.SchemeModuleOriginalCovariantExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- Statement only of actual exactness at one fixed original source O,
with the SAME actual global Ext roof and original zero augmentation.
It contains NO relative-Ext premise;the next theorem proves it under
explicit vanishings. It is not a verified proof by being defined. -/
def schemeModuleOriginalCovariantAtSourceStatement
    (C : ChainComplex X.Modules ℕ) {E M : X.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M) (O : X.Modules) : Prop :=
    (∀ x : Ext O M r,∃ y : O ⟶ E,
      (Ext.mk₀ y).comp (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha phi.hom
        (hAbove.eq_of_src _ _)) (zero_add r) = x) ∧
    (∀ x : O ⟶ E,
      (Ext.mk₀ x).comp (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha phi.hom
        (hAbove.eq_of_src _ _)) (zero_add r) = 0 ↔
      ∃ z : O ⟶ C.X 0,z ≫ alpha.f 0 = x)
/-- Reuse proved actual original exactness,with its hypotheses exposed;
no duplicate geometric Serre theorem is asserted. -/
theorem schemeModuleOriginalCovariantAtSourceStatement_proof
    (C : ChainComplex X.Modules ℕ) {E M : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M) (O : X.Modules)
    (hvan : ∀ j,j < r → ∀ q,0 < q → Subsingleton (Ext O (C.X (r-j-1)) q)) :
    schemeModuleOriginalCovariantAtSourceStatement C r alpha hAlpha hAbove phi O :=
  schemeModuleOriginalCovariantExactStatement_proof C r hr alpha hAlpha hAbove phi O hvan
end LinearStudy
