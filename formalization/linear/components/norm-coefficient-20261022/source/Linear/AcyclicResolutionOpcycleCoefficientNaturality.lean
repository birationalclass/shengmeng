module
public import Linear.AcyclicGlobalExtIteratedCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- The SAME actual acyclic-resolution Ext/opcycle equivalence commutes
with coefficient maps. Original resolution,source augmentation and unsigned
Yoneda boundary conventions are retained;no desired naturality premise. -/
theorem acyclicResolutionGlobalExtOpcycleAddEquiv_coefficient_naturality
    (K : ChainComplex A ℕ) (Z : A) (f : K ⟶ (ChainComplex.single₀ A).obj Z)
    [QuasiIso f] {F G : A} (a : F ⟶ G)
    (hF : ∀ p j,Subsingleton (Ext (K.X p) F (j+1)))
    (hG : ∀ p j,Subsingleton (Ext (K.X p) G (j+1)))
    (q : ℕ) (z : Ext Z F (q+1)) :
    acyclicResolutionGlobalExtOpcycleAddEquiv K Z f G hG q
      (z.comp (Ext.mk₀ a) (add_zero (q+1))) =
      (acyclicResolutionGlobalExtOpcycleAddEquiv K Z f F hF q z).comp
        (Ext.mk₀ a) (add_zero 1) := by
  have hK (p : ℕ) : K.ExactAt (p+1) :=
    (exactAt_iff_of_quasiIsoAt f (p+1)).mpr (ChainComplex.exactAt_succ_single_obj Z p)
  unfold acyclicResolutionGlobalExtOpcycleAddEquiv
  dsimp only [AddEquiv.trans_apply]
  rw [acyclicResolutionExtSourceIsoAddEquiv_coefficient_naturality]
  exact extAddEquivIndexTransport_coefficient_naturality
    (K.opcycles 0) (fun j => K.opcycles j) a
    (acyclicChainOpcycleIteratedGlobalExtAddEquiv K F hK hF 0 q)
    (acyclicChainOpcycleIteratedGlobalExtAddEquiv K G hK hG 0 q)
    (acyclicChainOpcycleIteratedGlobalExtAddEquiv_coefficient_naturality K a hK hF hG 0 q)
    rfl (Nat.zero_add q) (acyclicResolutionExtSourceIsoAddEquiv (chainResolutionOpcycleZeroIso K Z f) F (q+1) z)
end LinearStudy
