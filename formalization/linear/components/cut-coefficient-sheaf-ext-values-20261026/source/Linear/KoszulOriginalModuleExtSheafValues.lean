module
public import Linear.KoszulNativeCoextensionOriginalValues
public import Linear.TildePushforwardMappedUnitValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
/-- ACTUAL associated sheaf of derived MODULE Ext,ACTUAL original cut
pushforward and ACTUAL original representative/global-section values.
This is deliberately not an identification with derived SHEAF Ext. -/
def koszulExactTopExtOriginalTwoSheafValuesStatement {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (p : ℕ) (H : Fin (p+1) → R)
    (N : ModuleCat.{u} R) (M : ModuleCat.{u} S) (U : Type u)
    (P : N → U → (ModuleCat.restrictScalars phi.hom).obj M → Prop)
    (P0 : N → (ModuleCat.restrictScalars phi.hom).obj M → Prop) : Prop :=
  ∃ he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j,
    ∃ e : tilde (ModuleCat.of R
        (Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (p+1))) ≅
          (Scheme.Modules.pushforward (Spec.map phi)).obj (tilde M),
      (∀ (a : (⋀[R]^(p+1) (Fin (p+1) → R)) →ₗ[R] N) v,
        P (a (topKoszulGenerator (p+1))) v
          (tildePushforwardOriginalGlobalValue phi M (ModuleCat.of R
            (Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (p+1))) e
              (koszulExactTopExtCoefficientRepresentative p H he N a))) ∧
      ∀ a,P0 (a (topKoszulGenerator (p+1)))
        (tildePushforwardOriginalGlobalValue phi M (ModuleCat.of R
          (Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (p+1))) e
            (koszulExactTopExtCoefficientRepresentative p H he N a))
/-- The ACTUAL native MODULE Ext equivalence gives the actual sheaf iso
and original global-section square. No sheaf comparison or value square
is supplied as a new assumption. -/
theorem koszulExactTopExtOriginalTwoSheafValuesStatement_of_moduleExt
    {R S : CommRingCat.{u}} (phi : R ⟶ S) (p : ℕ) (H : Fin (p+1) → R)
    (N : ModuleCat.{u} R) (M : ModuleCat.{u} S) (U : Type u)
    (P : N → U → (ModuleCat.restrictScalars phi.hom).obj M → Prop)
    (P0 : N → (ModuleCat.restrictScalars phi.hom).obj M → Prop)
    (h : koszulExactTopExtOriginalTwoValuesStatement p H N
      ((ModuleCat.restrictScalars phi.hom).obj M) U P P0) :
    koszulExactTopExtOriginalTwoSheafValuesStatement phi p H N M U P P0 := by
  obtain ⟨he,hG⟩ := h
  refine ⟨he,?_⟩
  exact tildePushforward_existsOriginalTwoValues phi M
    (ModuleCat.of R (Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (p+1)))
    ((⋀[R]^(p+1) (Fin (p+1) → R)) →ₗ[R] N) U
    (fun a => koszulExactTopExtCoefficientRepresentative p H he N a)
    (fun a v => P (a (topKoszulGenerator (p+1))) v)
    (fun a => P0 (a (topKoszulGenerator (p+1)))) hG
end LinearStudy
