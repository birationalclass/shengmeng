module
public import Linear.AcyclicResolutionGlobalExtCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
/-- Actual coefficient map on SAME Hom/opcycle cokernel,using native
additive Yoneda naturality and native cokernel.map. -/
def acyclicChainOpcycleHomCokernelCoefficientMap (K : ChainComplex A ℕ)
    {F G : A} (a : F ⟶ G) (p : ℕ) :
    cokernel (acyclicChainOpcycleHomPrecompose K F p) ⟶
      cokernel (acyclicChainOpcycleHomPrecompose K G p) :=
  cokernel.map _ _ ((preadditiveYoneda.map a).app (op (K.X p)))
    ((preadditiveYoneda.map a).app (op (K.opcycles (p+1))))
    ((preadditiveYoneda.map a).naturality (K.fromOpcycles (p+1) p).op)
/-- The SAME actual quotient projection commutes with coefficient maps. -/
theorem acyclicChainOpcycleHomCokernelCoefficientMap_projection (K : ChainComplex A ℕ)
    {F G : A} (a : F ⟶ G) (p : ℕ) :
    cokernel.π (acyclicChainOpcycleHomPrecompose K F p) ≫
      acyclicChainOpcycleHomCokernelCoefficientMap K a p =
      (preadditiveYoneda.map a).app (op (K.opcycles (p+1))) ≫
        cokernel.π (acyclicChainOpcycleHomPrecompose K G p) :=
  cokernel.π_desc _ _ _
/-- SAME unsigned global Yoneda source boundary commutes with actual
postcomposition of Hom coefficients. No signed-delta identification. -/
theorem acyclicChainOpcycleHomGlobalExtBoundary_coefficient_naturality
    (K : ChainComplex A ℕ) {F G : A} (a : F ⟶ G) (p : ℕ)
    (hK : K.ExactAt (p+1)) (b : K.opcycles (p+1) ⟶ F) :
    acyclicChainOpcycleHomGlobalExtBoundary K G p hK (b ≫ a) =
      (acyclicChainOpcycleHomGlobalExtBoundary K F p hK b).comp (Ext.mk₀ a) (add_zero 1) := by
  change (chainOpcycleSequence_shortExact K p hK).extClass.comp (Ext.mk₀ (b ≫ a)) rfl =
    ((chainOpcycleSequence_shortExact K p hK).extClass.comp (Ext.mk₀ b) rfl).comp
      (Ext.mk₀ a) (add_zero 1)
  rw [← Ext.mk₀_comp_mk₀]
  exact (Ext.comp_assoc_of_third_deg_zero
    (chainOpcycleSequence_shortExact K p hK).extClass (Ext.mk₀ b) (Ext.mk₀ a) rfl).symm
/-- The actual original Hom-cokernel/global-Ext1 isomorphism is natural
in coefficients. This proves compatibility of the existing comparison. -/
theorem acyclicChainOpcycleHomGlobalExtCokernelIso_coefficient_naturality
    (K : ChainComplex A ℕ) {F G : A} (a : F ⟶ G) (p : ℕ)
    (hK : K.ExactAt (p+1)) [Subsingleton (Ext (K.X p) F 1)]
    [Subsingleton (Ext (K.X p) G 1)] :
    acyclicChainOpcycleHomCokernelCoefficientMap K a p ≫
      (acyclicChainOpcycleHomGlobalExtCokernelIso K G p hK).hom =
      (acyclicChainOpcycleHomGlobalExtCokernelIso K F p hK).hom ≫
        AddCommGrpCat.ofHom ((Ext.mk₀ a).postcomp (K.opcycles p) (add_zero 1)) := by
  apply (cancel_epi (cokernel.π (acyclicChainOpcycleHomPrecompose K F p))).1
  rw [← Category.assoc,acyclicChainOpcycleHomCokernelCoefficientMap_projection,
    Category.assoc,acyclicChainOpcycleHomGlobalExtCokernelIso_projection,
    ← Category.assoc,acyclicChainOpcycleHomGlobalExtCokernelIso_projection]
  ext b
  exact acyclicChainOpcycleHomGlobalExtBoundary_coefficient_naturality K a p hK b
end LinearStudy
