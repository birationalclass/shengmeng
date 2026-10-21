module
public import Linear.AcyclicResolutionGlobalExtShift
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
/-- The SAME unsigned Yoneda source-boundary equivalence is natural in
actual coefficients. This begins calibration of actual Cech/H duality. -/
theorem relativeAcyclicContravariantBoundaryAddEquiv_coefficient_naturality
    {F G : A} (a : F ⟶ G) {S : ShortComplex A} (hS : S.ShortExact)
    (n m : ℕ) (hm : 1+n=m)
    [Subsingleton (Ext S.X₂ F n)] [Subsingleton (Ext S.X₂ F m)]
    [Subsingleton (Ext S.X₂ G n)] [Subsingleton (Ext S.X₂ G m)]
    (z : Ext S.X₁ F n) :
    relativeAcyclicContravariantBoundaryAddEquiv G hS n m hm (z.comp (Ext.mk₀ a) (add_zero n)) =
      (relativeAcyclicContravariantBoundaryAddEquiv F hS n m hm z).comp (Ext.mk₀ a) (add_zero m) := by
  change hS.extClass.comp (z.comp (Ext.mk₀ a) (add_zero n)) hm =
    (hS.extClass.comp z hm).comp (Ext.mk₀ a) (add_zero m)
  exact (Ext.comp_assoc_of_third_deg_zero hS.extClass z (Ext.mk₀ a) hm).symm
/-- Inverse dimension shifting preserves SAME coefficient maps as well. -/
theorem relativeAcyclicContravariantBoundaryAddEquiv_symm_coefficient_naturality
    {F G : A} (a : F ⟶ G) {S : ShortComplex A} (hS : S.ShortExact)
    (n m : ℕ) (hm : 1+n=m)
    [Subsingleton (Ext S.X₂ F n)] [Subsingleton (Ext S.X₂ F m)]
    [Subsingleton (Ext S.X₂ G n)] [Subsingleton (Ext S.X₂ G m)]
    (z : Ext S.X₃ F m) :
    (relativeAcyclicContravariantBoundaryAddEquiv G hS n m hm).symm
      (z.comp (Ext.mk₀ a) (add_zero m)) =
      ((relativeAcyclicContravariantBoundaryAddEquiv F hS n m hm).symm z).comp (Ext.mk₀ a) (add_zero n) := by
  apply (relativeAcyclicContravariantBoundaryAddEquiv G hS n m hm).injective
  rw [AddEquiv.apply_symm_apply,relativeAcyclicContravariantBoundaryAddEquiv_coefficient_naturality,
    AddEquiv.apply_symm_apply]
/-- The ACTUAL opcycle global-Ext shift commutes with coefficient maps,
using the original short exact sequence and unsigned Yoneda convention. -/
theorem acyclicChainOpcycleGlobalExtShiftAddEquiv_coefficient_naturality
    (K : ChainComplex A ℕ) {F G : A} (a : F ⟶ G) (p q : ℕ) (hK : K.ExactAt (p+1))
    (hF : ∀ j,Subsingleton (Ext (K.X p) F (j+1)))
    (hG : ∀ j,Subsingleton (Ext (K.X p) G (j+1)))
    (z : Ext (K.opcycles p) F (q+2)) :
    acyclicChainOpcycleGlobalExtShiftAddEquiv K G p q hK hG (z.comp (Ext.mk₀ a) (add_zero (q+2))) =
      (acyclicChainOpcycleGlobalExtShiftAddEquiv K F p q hK hF z).comp (Ext.mk₀ a) (add_zero (q+1)) := by
  letI : Subsingleton (Ext (chainOpcycleSequence K p).X₂ F (q+1)) := hF q
  letI : Subsingleton (Ext (chainOpcycleSequence K p).X₂ F (q+2)) := hF (q+1)
  letI : Subsingleton (Ext (chainOpcycleSequence K p).X₂ G (q+1)) := hG q
  letI : Subsingleton (Ext (chainOpcycleSequence K p).X₂ G (q+2)) := hG (q+1)
  exact relativeAcyclicContravariantBoundaryAddEquiv_symm_coefficient_naturality a
    (chainOpcycleSequence_shortExact K p hK) (q+1) (q+2) (by omega) z
end LinearStudy
