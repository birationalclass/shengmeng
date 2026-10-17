module
public import Linear.SchemeModuleOriginalPositiveBoundaryIso
public import Linear.SchemeModuleOriginalNatClassImage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- The actual last original quotient isomorphism,transported to derived internal Ext at original E. -/
def schemeModuleOriginalNatTargetExtIso
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha) :
    schemeModuleInternalExt (C.opcycles (r-r)) N r ≅ schemeModuleInternalExt E N r :=
  schemeModuleInternalExtSourceIso
      (originalChainAsCochainOpcyclesIso C (cochainSourceDegree r r) (r-r)
        (by rw [cochainSourceDegree_eq];omega)).symm N r ≪≫
    schemeModuleInternalExtSourceIso (originalChainTerminalSourceIso C r alpha hAlpha) N r
/-- Its hom is EXACT the already proved original terminal map;no arbitrary comparison is provided. -/
theorem schemeModuleOriginalNatTargetExtIso_hom
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha) :
    (schemeModuleOriginalNatTargetExtIso C N r alpha hAlpha).hom =
      schemeModuleOriginalOpcycleExtComparison C N r r ≫
        schemeModuleInternalExtSourceMap (originalChainTerminalSourceIso C r alpha hAlpha).inv N r := by
  rw [schemeModuleOriginalOpcycleExtComparison_eq C N r r le_rfl]
  rfl
/-- FULL native sequence factors into the SAME first degree-zero source boundary and SAME invertible positive tail. -/
theorem schemeModuleOriginalNatIteratedBoundary_factor
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (p : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (I : InjectiveResolution N)
    (hA : ∀ j q,IsZero (schemeModuleInternalExt (C.X j) N (q+1))) :
    letI := hAlpha
    schemeModuleOriginalNatIteratedBoundary C N (p+1) alpha hAlpha (p+1) =
      schemeModuleInternalExtSourceBoundaryViaResolution (schemeModuleChainOpcycleSequence C p)
        (schemeModuleChainOpcycleSequence_shortExact C p (originalChainAugmentation_exactAt_succ C alpha p)) N I 0 ≫
      (schemeModuleOriginalNatPositiveTailIso C N (p+1) alpha hAlpha I hA (p+1) (by omega) le_rfl).hom := by
  letI := hAlpha
  rw [schemeModuleOriginalNatPositiveTailIso_hom]
  dsimp only [schemeModuleOriginalNatIteratedBoundary]
  rw [Functor.OfSequence.map_comp _ 0 1 (p+1) (by omega) (by omega),
    Functor.OfSequence.map_le_succ,
    schemeModuleOriginalNatBoundaryStep_eq C N (p+1) alpha hAlpha 0 (by omega)]
  simp only [Nat.zero_add,Nat.sub_zero,Nat.add_sub_cancel_right,eqToHom_refl,Category.id_comp]
  rw [schemeModuleInternalExtSourceBoundary_eq_viaResolution _ _ N I 0]
  congr 2
end LinearStudy
