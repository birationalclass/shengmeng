module
public import Linear.OriginalChainAugmentationClassZero
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
/-- The SAME ORIGINAL small-universe geometric class is killed by its
actual zero augmentation. Native universe transport and actual roofs
are identified by proved equations;no derived class is replaced. -/
theorem schemeModuleOriginalSmallClass_augmentation_precomp_zero
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    (Ext.mk₀ (alpha.f 0)).comp
      (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha)
        (zero_add r) = 0 := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  rw [schemeModuleOriginalChainTopExtClassSmall_eq_native]
  exact originalChainTopExtClass_augmentation_precomp_zero C r hr alpha a ha

/-- For the actual whole-cut source iso e,the annihilating morphism is
literally the original cokernel projection followed by that SAME e. -/
theorem schemeModuleOriginalSmallClass_quotient_precomp_zero
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ) (hr : 0 < r)
    (e : cokernel (C.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation C E e))
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    (Ext.mk₀ (cokernel.π (C.d 1 0) ≫ e.hom)).comp
      (schemeModuleOriginalChainTopExtClassSmall C r
        (originalChainCokernelTargetAugmentation C E e) he a ha) (zero_add r) = 0 := by
  simpa only [originalChainCokernelTargetAugmentation_f_zero] using
    schemeModuleOriginalSmallClass_augmentation_precomp_zero C r hr
      (originalChainCokernelTargetAugmentation C E e) he a ha

/-- Statement only:every actual top-functional class lies in the kernel
of precomposition by the SAME original zero augmentation. -/
def schemeModuleOriginalClassAugmentationZeroStatement
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha) : Prop :=
    ∀ (N : X.Modules) (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0),
      (Ext.mk₀ (alpha.f 0)).comp
        (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha)
          (zero_add r) = 0
/-- Actual kernel containment for all coefficients is proved from the
original roof construction;no cohomology or class-vanishing input. -/
theorem schemeModuleOriginalClassAugmentationZeroStatement_proof
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha) :
    schemeModuleOriginalClassAugmentationZeroStatement C r alpha hAlpha :=
  fun N a ha => schemeModuleOriginalSmallClass_augmentation_precomp_zero C r hr alpha hAlpha a ha
end LinearStudy
