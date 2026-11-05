module
public import Linear.AcyclicGlobalExtCoefficientNaturality
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
/-- Transport in actual Ext degree/object indices preserves coefficient
naturality. This only transports proved equal indices,no new Ext model. -/
theorem extAddEquivIndexTransport_coefficient_naturality
    (P : A) (Q : ℕ → A) {F G : A} (a : F ⟶ G) {n n' i i' : ℕ}
    (eF : Ext P F n ≃+ Ext (Q i) F 1) (eG : Ext P G n ≃+ Ext (Q i) G 1)
    (hNat : ∀ z,eG (z.comp (Ext.mk₀ a) (add_zero n)) = (eF z).comp (Ext.mk₀ a) (add_zero 1))
    (hn : n=n') (hi : i=i') (z : Ext P F n') :
    ((congrArg₂ (fun d j => Ext P G d ≃+ Ext (Q j) G 1) hn hi).mp eG)
      (z.comp (Ext.mk₀ a) (add_zero n')) =
      (((congrArg₂ (fun d j => Ext P F d ≃+ Ext (Q j) F 1) hn hi).mp eF) z).comp
        (Ext.mk₀ a) (add_zero 1) := by
  cases hn
  cases hi
  exact hNat z
/-- ALL iterated actual opcycle Ext shifts commute with SAME coefficient
maps. Index transports retain original degrees;no naturality is an input. -/
theorem acyclicChainOpcycleIteratedGlobalExtAddEquiv_coefficient_naturality
    (K : ChainComplex A ℕ) {F G : A} (a : F ⟶ G)
    (hK : ∀ p,K.ExactAt (p+1))
    (hF : ∀ p j,Subsingleton (Ext (K.X p) F (j+1)))
    (hG : ∀ p j,Subsingleton (Ext (K.X p) G (j+1)))
    (p q : ℕ) (z : Ext (K.opcycles p) F (q+1)) :
    acyclicChainOpcycleIteratedGlobalExtAddEquiv K G hK hG p q
      (z.comp (Ext.mk₀ a) (add_zero (q+1))) =
      (acyclicChainOpcycleIteratedGlobalExtAddEquiv K F hK hF p q z).comp (Ext.mk₀ a) (add_zero 1) := by
  induction q generalizing p with
  | zero => rfl
  | succ q ih =>
    let eF := (acyclicChainOpcycleGlobalExtShiftAddEquiv K F p q (hK p) (hF p)).trans
      (acyclicChainOpcycleIteratedGlobalExtAddEquiv K F hK hF (p+1) q)
    let eG := (acyclicChainOpcycleGlobalExtShiftAddEquiv K G p q (hK p) (hG p)).trans
      (acyclicChainOpcycleIteratedGlobalExtAddEquiv K G hK hG (p+1) q)
    have hNat : ∀ z,eG (z.comp (Ext.mk₀ a) (add_zero (q+2))) =
        (eF z).comp (Ext.mk₀ a) (add_zero 1) := by
      intro z
      dsimp only [eF,eG,AddEquiv.trans_apply]
      rw [acyclicChainOpcycleGlobalExtShiftAddEquiv_coefficient_naturality,ih]
    exact extAddEquivIndexTransport_coefficient_naturality (K.opcycles p) (fun j => K.opcycles j) a
      (n:=q+2) (n':=q+1+1) (i:=(p+1)+q) (i':=p+(q+1)) eF eG hNat
      (by omega) (by omega) z
/-- SAME native source-isomorphism transport of Ext commutes with actual
coefficient maps,by Yoneda associativity with degree-zero morphisms. -/
theorem acyclicResolutionExtSourceIsoAddEquiv_coefficient_naturality
    {P Q F G : A} (e : P ≅ Q) (a : F ⟶ G) (n : ℕ) (z : Ext Q F n) :
    acyclicResolutionExtSourceIsoAddEquiv e G n (z.comp (Ext.mk₀ a) (add_zero n)) =
      (acyclicResolutionExtSourceIsoAddEquiv e F n z).comp (Ext.mk₀ a) (add_zero n) := by
  rw [acyclicResolutionExtSourceIsoAddEquiv_apply,acyclicResolutionExtSourceIsoAddEquiv_apply]
  exact (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ e.hom) z (Ext.mk₀ a) (zero_add n)).symm
end LinearStudy
