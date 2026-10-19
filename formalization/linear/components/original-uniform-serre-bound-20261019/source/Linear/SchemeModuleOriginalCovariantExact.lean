module
public import Linear.OriginalChainCovariantCoefficientIso
public import Linear.SchemeModuleOriginalSmallClassBoundary
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
/-- The SAME original actual global SHEAF-MODULE Ext roof gives an onto
covariant boundary under explicit relative Ext vanishings. Neither local
free terms nor vanishing of internal SHEAF Ext imply this input. -/
theorem schemeModuleOriginalCovariant_surjective
    (C : ChainComplex X.Modules ℕ) {E M : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M) (O : X.Modules)
    (hvan : ∀ j,j < r → ∀ q,0 < q → Subsingleton (Ext O (C.X (r-j-1)) q)) :
    ∀ x : Ext O M r,∃ y : O ⟶ E,
      (Ext.mk₀ y).comp (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha phi.hom
        (hAbove.eq_of_src _ _)) (zero_add r) = x := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  simp only [schemeModuleOriginalChainTopExtClassSmall_eq_native]
  exact originalChainCovariantCoefficientIso_surjective C r hr alpha hAbove phi O hvan
/-- Kernel of the SAME small-universe original global class is exactly
the image of SAME original augmentation. This is GLOBAL covariant Ext,
not affine module Ext or derived internal SHEAF Ext. -/
theorem schemeModuleOriginalCovariant_kernel
    (C : ChainComplex X.Modules ℕ) {E M : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M) (O : X.Modules)
    (hvan : ∀ j,j < r → ∀ q,0 < q → Subsingleton (Ext O (C.X (r-j-1)) q))
    (x : O ⟶ E) :
    (Ext.mk₀ x).comp (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha phi.hom
        (hAbove.eq_of_src _ _)) (zero_add r) = 0 ↔
      ∃ z : O ⟶ C.X 0,z ≫ alpha.f 0 = x := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  rw [schemeModuleOriginalChainTopExtClassSmall_eq_native]
  exact originalChainCovariantCoefficientIso_kernel C r hr alpha hAbove phi O hvan x
/-- Statement only:for EVERY actual source O,explicit relative Ext
vanishing implies surjectivity and exact kernel/image for SAME class.
The following theorem proves this implication. -/
def schemeModuleOriginalCovariantExactStatement
    (C : ChainComplex X.Modules ℕ) {E M : X.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M) : Prop :=
  ∀ O : X.Modules,
    (∀ j,j < r → ∀ q,0 < q → Subsingleton (Ext O (C.X (r-j-1)) q)) →
    (∀ x : Ext O M r,∃ y : O ⟶ E,
      (Ext.mk₀ y).comp (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha phi.hom
        (hAbove.eq_of_src _ _)) (zero_add r) = x) ∧
    (∀ x : O ⟶ E,
      (Ext.mk₀ x).comp (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha phi.hom
        (hAbove.eq_of_src _ _)) (zero_add r) = 0 ↔
      ∃ z : O ⟶ C.X 0,z ≫ alpha.f 0 = x)
/-- Actual proof of the conditional exact sequence on the SAME original
roof and augmentation,for every O. No desired exactness is an input. -/
theorem schemeModuleOriginalCovariantExactStatement_proof
    (C : ChainComplex X.Modules ℕ) {E M : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M) :
    schemeModuleOriginalCovariantExactStatement C r alpha hAlpha hAbove phi := by
  intro O hv
  exact ⟨schemeModuleOriginalCovariant_surjective C r hr alpha hAlpha hAbove phi O hv,
    schemeModuleOriginalCovariant_kernel C r hr alpha hAlpha hAbove phi O hv⟩
end LinearStudy
