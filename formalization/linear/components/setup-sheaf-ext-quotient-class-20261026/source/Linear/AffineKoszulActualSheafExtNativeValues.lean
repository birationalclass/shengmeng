module
public import Linear.AffineKoszulOriginalSheafExtQuotientClass
public import Linear.TildePushforwardMappedUnitValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- Actual derived SHEAF Ext,original roof/canonical lambda class diagram,
and original native coefficient values with ONE actual coefficient iso.
The exact source witness and coefficient iso precede ALL resolutions and
ALL original representatives. Statement only;fixed C_L/top-H stay open. -/
def affineKoszulActualSheafExtNativeTwoValuesStatement {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (p : ℕ) (H : Fin (p+1) → R)
    (N : ModuleCat.{u} R) (M : ModuleCat.{u} S) (U : Type u)
    (P : N → U → (ModuleCat.restrictScalars phi.hom).obj M → Prop)
    (P0 : N → (ModuleCat.restrictScalars phi.hom).obj M → Prop) : Prop :=
  ∃ he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j,
    ∃ e : tilde (ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)))) ≅
        (Scheme.Modules.pushforward (Spec.map phi)).obj (tilde M),
      (∀ I : InjectiveResolution (tilde N),
        ∃ chi : schemeModuleInternalExt (tildeKoszulOriginalCutCokernelCofork R H).pt (tilde N) (p+1) ≅
            (Scheme.Modules.pushforward (Spec.map phi)).obj (tilde M),
          schemeModuleOriginalTopExtClassIsoLaw (tildeFunctionKoszulComplex R H) (p+1)
            (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
              (tildeKoszulOriginalCutCokernelCofork R H))
            (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he) chi
            (affineKoszulOriginalTopCoefficientQuotientMap R N p H ≫ e.hom)) ∧
      (∀ x v,P x v (tildePushforwardOriginalGlobalValue phi M
        (ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)))) e
          (Submodule.Quotient.mk x))) ∧
      ∀ x,P0 x (tildePushforwardOriginalGlobalValue phi M
        (ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)))) e
          (Submodule.Quotient.mk x))
/-- Derive the actual SHEAF Ext/native-target original-class diagram and
original global coefficient values from ACTUAL original coefficient
module duality. No SHEAF Ext iso or desired class square is assumed. -/
theorem affineKoszulActualSheafExtNativeTwoValuesStatement_of_coefficient
    {R S : CommRingCat.{u}} (phi : R ⟶ S) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (N : ModuleCat.{u} R) (M : ModuleCat.{u} S) (U : Type u)
    (P : N → U → (ModuleCat.restrictScalars phi.hom).obj M → Prop)
    (P0 : N → (ModuleCat.restrictScalars phi.hom).obj M → Prop)
    (h : ∃ F : (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N))) ≃ₗ[R]
        (ModuleCat.restrictScalars phi.hom).obj M,
      (∀ x v,P x v (F (Submodule.Quotient.mk x))) ∧
        ∀ x,P0 x (F (Submodule.Quotient.mk x))) :
    affineKoszulActualSheafExtNativeTwoValuesStatement phi p H N M U P P0 := by
  obtain ⟨e,hP,hP0⟩ := tildePushforward_existsOriginalTwoValues phi M
    (ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)))) N U
    (fun x => Submodule.Quotient.mk x) P P0 h
  refine ⟨he,e,?_,hP,hP0⟩
  intro I
  refine ⟨affineKoszulOriginalSheafExtQuotientIso R N p H he I ≪≫ e,?_⟩
  exact schemeModuleOriginalTopExtClassIsoLaw_postcompose
    (tildeFunctionKoszulComplex R H) (p+1)
    (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H))
    (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he)
    (affineKoszulOriginalSheafExtQuotientIso R N p H he I)
    (affineKoszulOriginalTopCoefficientQuotientMap R N p H)
    (affineKoszulOriginalSheafExtQuotientIso_classLaw R N p H he I) e
end LinearStudy
