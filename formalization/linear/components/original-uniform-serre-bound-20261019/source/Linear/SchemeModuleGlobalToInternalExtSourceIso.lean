module
public import Linear.SchemeModuleHomZeroSourceNaturality
public import Linear.SchemeModuleFiniteFreeFrameInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- Retain the ACTUAL target source sheaf of the original class,not just its pullback along a canonical source isomorphism. -/
theorem schemeModuleGlobalToInternalExtAll_sourceIso {P Q : X.Modules}
    (e : P ≅ Q) (N : X.Modules) (q : ℕ) (x : Ext.{u} Q N q) :
    schemeModuleGlobalToInternalExtAll Q N q x =
      schemeModuleGlobalToInternalExtAll P N q ((Ext.mk₀ e.hom).comp x (zero_add q)) ≫
        (schemeModuleInternalExtSourceIso e N q).hom := by
  apply (cancel_mono (schemeModuleInternalExtSourceIso e N q).inv).1
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  exact (schemeModuleGlobalToInternalExtAll_sourceNaturality e.hom q x).symm
end LinearStudy
