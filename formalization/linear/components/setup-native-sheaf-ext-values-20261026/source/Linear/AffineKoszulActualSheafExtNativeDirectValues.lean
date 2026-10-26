module
public import Linear.AffineKoszulActualSheafExtNativeValues
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
/-- Direct target-carrier interface for the SAME generic native class and
value statement. The scalar-restriction carrier is literally M;hide the
restriction functor from concrete predicate elaboration. Statement only. -/
def affineKoszulActualSheafExtNativeDirectValuesStatement {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (p : ℕ) (H : Fin (p+1) → R)
    (N : ModuleCat.{u} R) (M : ModuleCat.{u} S) (U : Type u)
    (P : N → U → M → Prop) (P0 : N → M → Prop) : Prop :=
  affineKoszulActualSheafExtNativeTwoValuesStatement phi p H N M U P P0
/-- Derive the actual SHEAF Ext/native-target original-class diagram and
original global coefficient values from ACTUAL original coefficient
module duality. No SHEAF Ext iso or desired class square is assumed. -/
theorem affineKoszulActualSheafExtNativeDirectValuesStatement_of_coefficient
    {R S : CommRingCat.{u}} (phi : R ⟶ S) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (N : ModuleCat.{u} R) (M : ModuleCat.{u} S) (U : Type u)
    (P : N → U → M → Prop)
    (P0 : N → M → Prop)
    (h : ∃ F : (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N))) ≃ₗ[R]
        (ModuleCat.restrictScalars phi.hom).obj M,
      (∀ x v,P x v (F (Submodule.Quotient.mk x))) ∧
        ∀ x,P0 x (F (Submodule.Quotient.mk x))) :
    affineKoszulActualSheafExtNativeDirectValuesStatement phi p H N M U P P0 := by
  exact affineKoszulActualSheafExtNativeTwoValuesStatement_of_coefficient phi p H he N M U P P0 h
end LinearStudy
