module
public import Linear.SchemeModuleOriginalWholeTopCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- Exact calibration law for ALL original top functionals,using ONE
specified iso and ONE specified Hom restriction map. This is a statement,
not a proof. The original class is its actual roof followed by canonical
lambda, never a class defined by the inverse of chi. -/
def schemeModuleOriginalTopExtClassIsoLaw
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    {T : X.Modules} (chi : schemeModuleInternalExt E N r ≅ T)
    (g : schemeModuleHomModuleSheaf (C.X r) N ⟶ T) : Prop :=
  letI := HasDerivedCategory.standard X.Modules
  ∀ (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0),
    schemeModuleGlobalToInternalExtAll E N r
        (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha) ≫ chi.hom =
      (schemeModuleHomUnitAddEquiv (C.X r) N).toEquiv.symm a ≫ g
/-- The previously verified whole original boundary calculation proves
the law for SAME actual Hom cokernel,uniformly for every representative. -/
theorem schemeModuleOriginalTopExtClassIsoLaw_wholeCokernel
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (p : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (I : InjectiveResolution N)
    (hA : ∀ j q,IsZero (schemeModuleInternalExt (C.X j) N (q+1)))
    (hAbove : IsZero (C.X (p+2))) :
    schemeModuleOriginalTopExtClassIsoLaw C (p+1) alpha hAlpha
      (schemeModuleOriginalWholeTopCokernelIso C N p alpha hAlpha I hA hAbove)
      (cokernel.π (schemeModuleHomPrecompose (N:=N) (C.d (p+1) p))) := by
  intro a ha
  exact schemeModuleOriginalSmallClass_wholeTopCokernel C p alpha hAlpha I hA hAbove a ha
/-- Transport the proved representative law through an actual target iso.
The SAME original class and SAME functional are retained for all a. -/
theorem schemeModuleOriginalTopExtClassIsoLaw_postcompose
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    {T U : X.Modules} (chi : schemeModuleInternalExt E N r ≅ T)
    (g : schemeModuleHomModuleSheaf (C.X r) N ⟶ T)
    (h : schemeModuleOriginalTopExtClassIsoLaw C r alpha hAlpha chi g) (e : T ≅ U) :
    schemeModuleOriginalTopExtClassIsoLaw C r alpha hAlpha (chi ≪≫ e) (g ≫ e.hom) := by
  intro a ha
  change _ ≫ (chi.hom ≫ e.hom) = _
  rw [← Category.assoc,h a ha,Category.assoc]
end LinearStudy
