module
public import Linear.SchemeModuleExtTracePairing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u v
variable {X : Scheme.{u}} {D E W : X.Modules} {r : ℕ}
variable {K : Type v} [AddCommGroup K]
/-- The original section/unit-Hom identification respects EVERY actual
source morphism. This extends the already proved scalar instance by
reusing the actual global-section morphism naturality. -/
theorem schemeModuleUnitHomGlobalSections_symm_map
    (b : D ⟶ E) (s : Γ(D,⊤)) :
    (schemeModuleUnitHomGlobalSectionsAddEquiv X E).symm (b.app ⊤ s) =
      (schemeModuleUnitHomGlobalSectionsAddEquiv X D).symm s ≫ b := by
  exact moduleSheafGlobalSectionMorphism_postcompose D b s
/-- The SAME global Ext/section trace pairing is contravariantly natural
in the actual source. The formula uses the original Yoneda class and
trace. No proper-duality, local perfection or normalization premise. -/
theorem schemeModuleExtSectionTracePairing_source_naturality
    (b : D ⟶ E)
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ K)
    (z : Ext.{u} E W r) (s : Γ(D,⊤)) :
    schemeModuleExtSectionTracePairing trace ((Ext.mk₀ b).comp z (zero_add r)) s =
      schemeModuleExtSectionTracePairing trace z (b.app ⊤ s) := by
  dsimp only [schemeModuleExtSectionTracePairing,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  rw [schemeModuleUnitHomGlobalSections_symm_map,Ext.mk₀_comp_mk₀_assoc]
/-- A source projector fixing the SAME Ext class forces its trace
functional to annihilate sections killed by that projector. Actual
projector/class identities remain explicit; no geometric support or
nondegeneracy conclusion is inserted as a hypothesis or claimed here. -/
theorem schemeModuleExtSectionTracePairing_zero_of_source_projector
    (b : E ⟶ E)
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ K)
    (z : Ext.{u} E W r)
    (hfix : (Ext.mk₀ b).comp z (zero_add r)=z)
    (s : Γ(E,⊤)) (hs : b.app ⊤ s=0) :
    schemeModuleExtSectionTracePairing trace z s=0 := by
  have h := schemeModuleExtSectionTracePairing_source_naturality b trace z s
  rw [hfix,hs,map_zero] at h
  exact h
end LinearStudy
