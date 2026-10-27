module
public import Linear.AcyclicResolutionOpcycleCoefficientNaturality
public import Linear.ChainActualHomHomologyCoefficientNaturality
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
/-- SAME actual unbounded acyclic-resolution comparison from global Ext
to Hom-cochain homology is natural in coefficients. Every shift,source
augmentation,Hom quotient and homology map is the existing actual one.
The standard SIGNED contravariant connecting map is still not identified. -/
theorem acyclicResolutionGlobalExtActualHomologyIso_coefficient_naturality
    (K : ChainComplex A ℕ) (Z : A) (f : K ⟶ (ChainComplex.single₀ A).obj Z)
    [QuasiIso f] {F G : A} (a : F ⟶ G)
    (hF : ∀ p j,Subsingleton (Ext (K.X p) F (j+1)))
    (hG : ∀ p j,Subsingleton (Ext (K.X p) G (j+1))) (q : ℕ) :
    AddCommGrpCat.ofHom ((Ext.mk₀ a).postcomp Z (add_zero (q+1))) ≫
      (acyclicResolutionGlobalExtActualHomologyIso K Z f G hG q).hom =
      (acyclicResolutionGlobalExtActualHomologyIso K Z f F hF q).hom ≫
        HomologicalComplex.homologyMap (chainActualHomCochainCoefficientMap K a) (q+1) := by
  have hK : K.ExactAt (q+1) :=
    (exactAt_iff_of_quasiIsoAt f (q+1)).mpr (ChainComplex.exactAt_succ_single_obj Z q)
  letI : Subsingleton (Ext (K.X q) F 1) := hF q 0
  letI : Subsingleton (Ext (K.X q) G 1) := hG q 0
  have hs : CommSq (AddCommGrpCat.ofHom ((Ext.mk₀ a).postcomp Z (add_zero (q+1))))
      (acyclicResolutionGlobalExtOpcycleAddEquiv K Z f F hF q).toAddCommGrpIso.hom
      (acyclicResolutionGlobalExtOpcycleAddEquiv K Z f G hG q).toAddCommGrpIso.hom
      (AddCommGrpCat.ofHom ((Ext.mk₀ a).postcomp (K.opcycles q) (add_zero 1))) := by
    constructor
    ext z
    exact acyclicResolutionGlobalExtOpcycleAddEquiv_coefficient_naturality K Z f a hF hG q z
  have hc : CommSq (AddCommGrpCat.ofHom ((Ext.mk₀ a).postcomp (K.opcycles q) (add_zero 1)))
      (acyclicChainOpcycleHomGlobalExtCokernelIso K F q hK).inv
      (acyclicChainOpcycleHomGlobalExtCokernelIso K G q hK).inv
      (acyclicChainOpcycleHomCokernelCoefficientMap K a q) :=
    CommSq.vert_inv (g:=acyclicChainOpcycleHomGlobalExtCokernelIso K F q hK)
      (h:=acyclicChainOpcycleHomGlobalExtCokernelIso K G q hK)
      ⟨acyclicChainOpcycleHomGlobalExtCokernelIso_coefficient_naturality K a q hK⟩
  have hh : CommSq (acyclicChainOpcycleHomCokernelCoefficientMap K a q)
      (chainActualHomCochainHomologyCokernelIso K F q).inv
      (chainActualHomCochainHomologyCokernelIso K G q).inv
      (HomologicalComplex.homologyMap (chainActualHomCochainCoefficientMap K a) (q+1)) :=
    CommSq.vert_inv (g:=chainActualHomCochainHomologyCokernelIso K F q)
      (h:=chainActualHomCochainHomologyCokernelIso K G q)
      ⟨chainActualHomCochainHomologyCokernelIso_coefficient_naturality K a q⟩
  exact (hs.vert_comp (hc.vert_comp hh)).w
end LinearStudy
