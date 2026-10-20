module
public import Linear.SchemeModuleActualGlobalSectionTransport
public import Linear.SchemeModuleOriginalCovariantSerreStatement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {D X : Scheme.{u}} (i : D ⟶ X) (L : D.Modules)
variable (C : ChainComplex X.Modules ℕ) {F M : X.Modules} (r : ℕ)
variable (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj ((Scheme.Modules.pushforward i).obj L))
variable (hAlpha : QuasiIso alpha) (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M)
/-- The SAME original actual boundary on global sections of the ORIGINAL
cut sheaf,via the canonical pushforward section equivalence. -/
def schemeModuleOriginalCutActualSectionBoundary : Γ(L,⊤) →+ schemeModuleActualCohomology X M r :=
  (schemeModuleOriginalActualSectionBoundary C r alpha hAlpha hAbove phi).comp
    (schemeModulePushforwardGlobalSectionsAddEquiv i L).symm.toAddMonoidHom
/-- The original augmentation on O(t)-sections,under a PROVED zero-term
isomorphism and the canonical pushforward section identification. -/
def schemeModuleOriginalCutActualSectionMap (zeroIso : C.X 0 ≅ F) :
    Γ(F,⊤) →+ Γ(L,⊤) :=
  (schemeModulePushforwardGlobalSectionsAddEquiv i L).toAddMonoidHom.comp
    ((zeroIso.inv ≫ alpha.f 0).app ⊤).hom
/-- Actual cut-section boundary is onto SAME native H whenever the SAME
original roof has its proved actual-section exactness. -/
theorem schemeModuleOriginalCutActualSectionBoundary_surjective
    (h : schemeModuleOriginalActualSectionExactStatement C r alpha hAlpha hAbove phi) :
    Function.Surjective (schemeModuleOriginalCutActualSectionBoundary i L C r alpha hAlpha hAbove phi) :=
  h.1.comp (schemeModulePushforwardGlobalSectionsAddEquiv i L).symm.surjective
/-- Kernel of the SAME cut-section boundary is exactly image of the
SAME original augmentation,now on the stated zero-term twist sections. -/
theorem schemeModuleOriginalCutActualSectionBoundary_kernel
    (zeroIso : C.X 0 ≅ F)
    (h : schemeModuleOriginalActualSectionExactStatement C r alpha hAlpha hAbove phi)
    (s : Γ(L,⊤)) :
    schemeModuleOriginalCutActualSectionBoundary i L C r alpha hAlpha hAbove phi s = 0 ↔
      ∃ z : Γ(F,⊤),schemeModuleOriginalCutActualSectionMap i L C alpha zeroIso z = s := by
  let e := schemeModulePushforwardGlobalSectionsAddEquiv i L
  change schemeModuleExtClassActualSectionBoundary _ (e.symm s) = 0 ↔ _
  rw [schemeModuleActualSectionBoundary_kernel_of_zeroIso (alpha.f 0) zeroIso _ h.2]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    exact (congrArg e hz).trans (e.apply_symm_apply s)
  · rintro ⟨z,hz⟩
    refine ⟨z,e.injective ?_⟩
    exact hz.trans (e.apply_symm_apply s).symm
/-- The actual cut-section sequence is exact,with genuine maps at both
ends. It still makes no proper-duality or prescribed-section assertion. -/
theorem schemeModuleOriginalCutActualSection_exact
    (zeroIso : C.X 0 ≅ F)
    (h : schemeModuleOriginalActualSectionExactStatement C r alpha hAlpha hAbove phi) :
    Function.Surjective (schemeModuleOriginalCutActualSectionBoundary i L C r alpha hAlpha hAbove phi) ∧
      ∀ s : Γ(L,⊤),schemeModuleOriginalCutActualSectionBoundary i L C r alpha hAlpha hAbove phi s = 0 ↔
        ∃ z : Γ(F,⊤),schemeModuleOriginalCutActualSectionMap i L C alpha zeroIso z = s :=
  ⟨schemeModuleOriginalCutActualSectionBoundary_surjective i L C r alpha hAlpha hAbove phi h,
    schemeModuleOriginalCutActualSectionBoundary_kernel i L C r alpha hAlpha hAbove phi zeroIso h⟩
end LinearStudy
