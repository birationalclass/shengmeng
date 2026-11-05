module
public import Linear.AcyclicResolutionGlobalExtShift
public import Mathlib.Algebra.Homology.ShortComplex.Ab
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
/-- Actual Hom precomposition by SAME original quotient-sequence source map. -/
def acyclicChainOpcycleHomPrecompose (K : ChainComplex A ℕ) (F : A) (p : ℕ) :
    AddCommGrpCat.of (K.X p ⟶ F) ⟶ AddCommGrpCat.of (K.opcycles (p+1) ⟶ F) :=
  (preadditiveYoneda.obj F).map (K.fromOpcycles (p+1) p).op
/-- Actual UNSIGNED Yoneda source boundary,normalized by native Hom/Ext^0.
This is a global group map,not internal sheaf Ext or a signed delta claim. -/
def acyclicChainOpcycleHomGlobalExtBoundary (K : ChainComplex A ℕ) (F : A) (p : ℕ)
    (hK : K.ExactAt (p+1)) : (K.opcycles (p+1) ⟶ F) →+ Ext (K.opcycles p) F 1 :=
  ((chainOpcycleSequence_shortExact K p hK).extClass.precomp F rfl).comp
    Ext.addEquiv₀.symm.toAddMonoidHom
/-- Boundary is ONTO from global term Ext^1 acyclicity. -/
theorem acyclicChainOpcycleHomGlobalExtBoundary_surjective
    (K : ChainComplex A ℕ) (F : A) (p : ℕ) (hK : K.ExactAt (p+1))
    [Subsingleton (Ext (K.X p) F 1)] :
    Function.Surjective (acyclicChainOpcycleHomGlobalExtBoundary K F p hK) := by
  letI : Subsingleton (Ext (chainOpcycleSequence K p).X₂ F 1) :=
    inferInstanceAs (Subsingleton (Ext (K.X p) F 1))
  intro x
  obtain ⟨z,hz⟩ := Ext.contravariant_sequence_exact₃
    (chainOpcycleSequence_shortExact K p hK) F x (Subsingleton.elim _ _) (n₀ := 0) rfl
  refine ⟨Ext.homEquiv₀ z,?_⟩
  change (chainOpcycleSequence_shortExact K p hK).extClass.comp
    (Ext.mk₀ (Ext.homEquiv₀ z)) rfl = x
  rw [Ext.mk₀_homEquiv₀_apply,hz]
/-- Kernel is precisely SAME original Hom precomposition image;
no projectivity,injectivity or desired comparison premise. -/
theorem acyclicChainOpcycleHomGlobalExtBoundary_kernel
    (K : ChainComplex A ℕ) (F : A) (p : ℕ) (hK : K.ExactAt (p+1))
    (a : K.opcycles (p+1) ⟶ F) :
    acyclicChainOpcycleHomGlobalExtBoundary K F p hK a = 0 ↔
      ∃ b : K.X p ⟶ F,K.fromOpcycles (p+1) p ≫ b = a := by
  let hS := chainOpcycleSequence_shortExact K p hK
  constructor
  · intro ha
    obtain ⟨z,hz⟩ := Ext.contravariant_sequence_exact₁ hS F (Ext.mk₀ a) rfl ha
    refine ⟨Ext.homEquiv₀ z,?_⟩
    apply (Ext.mk₀_bijective _ _).1
    rw [← Ext.mk₀_comp_mk₀,Ext.mk₀_homEquiv₀_apply]
    exact hz
  · rintro ⟨b,rfl⟩
    change hS.extClass.comp (Ext.mk₀ (K.fromOpcycles (p+1) p ≫ b)) rfl = 0
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ b)
/-- Actual global Hom-to-Ext presentation for SAME opcycle sequence. -/
def acyclicChainOpcycleHomGlobalExtPresentation (K : ChainComplex A ℕ) (F : A) (p : ℕ)
    (hK : K.ExactAt (p+1)) : ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (acyclicChainOpcycleHomPrecompose K F p)
    (AddCommGrpCat.ofHom (acyclicChainOpcycleHomGlobalExtBoundary K F p hK)) (by
      ext b
      change (chainOpcycleSequence_shortExact K p hK).extClass.comp
        (Ext.mk₀ (K.fromOpcycles (p+1) p ≫ b)) rfl = 0
      rw [← Ext.mk₀_comp_mk₀]
      exact (chainOpcycleSequence_shortExact K p hK).extClass_comp_assoc (Ext.mk₀ b))
/-- Exactness of ACTUAL global Hom-to-Ext presentation,derived from native LES. -/
theorem acyclicChainOpcycleHomGlobalExtPresentation_exact
    (K : ChainComplex A ℕ) (F : A) (p : ℕ) (hK : K.ExactAt (p+1)) :
    (acyclicChainOpcycleHomGlobalExtPresentation K F p hK).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro a ha
  exact (acyclicChainOpcycleHomGlobalExtBoundary_kernel K F p hK a).mp ha
/-- Global Ext^1 is the ACTUAL original Hom-precomposition cokernel. -/
def acyclicChainOpcycleHomGlobalExtCokernelIso
    (K : ChainComplex A ℕ) (F : A) (p : ℕ) (hK : K.ExactAt (p+1))
    [Subsingleton (Ext (K.X p) F 1)] :
    cokernel (acyclicChainOpcycleHomPrecompose K F p) ≅ AddCommGrpCat.of (Ext (K.opcycles p) F 1) := by
  letI : Epi (acyclicChainOpcycleHomGlobalExtPresentation K F p hK).g :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (acyclicChainOpcycleHomGlobalExtBoundary_surjective K F p hK)
  exact (cokernelIsCokernel (acyclicChainOpcycleHomPrecompose K F p)).coconePointUniqueUpToIso
    (acyclicChainOpcycleHomGlobalExtPresentation_exact K F p hK).gIsCokernel
/-- Its projection is precisely SAME original unsigned Yoneda boundary. -/
theorem acyclicChainOpcycleHomGlobalExtCokernelIso_projection
    (K : ChainComplex A ℕ) (F : A) (p : ℕ) (hK : K.ExactAt (p+1))
    [Subsingleton (Ext (K.X p) F 1)] :
    cokernel.π (acyclicChainOpcycleHomPrecompose K F p) ≫
      (acyclicChainOpcycleHomGlobalExtCokernelIso K F p hK).hom =
        AddCommGrpCat.ofHom (acyclicChainOpcycleHomGlobalExtBoundary K F p hK) := by
  letI : Epi (acyclicChainOpcycleHomGlobalExtPresentation K F p hK).g :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (acyclicChainOpcycleHomGlobalExtBoundary_surjective K F p hK)
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (acyclicChainOpcycleHomPrecompose K F p))
    (acyclicChainOpcycleHomGlobalExtPresentation_exact K F p hK).gIsCokernel WalkingParallelPair.one
/-- Actual acyclic resolution computes GLOBAL positive Ext by SAME final
Hom/opcycles cokernel. This is an explicit iso,not merely a vanishing criterion.
No signed connecting-map normalization or Cech/H comparison is asserted yet. -/
def acyclicResolutionGlobalExtHomCokernelIso
    (K : ChainComplex A ℕ) (Z : A) (f : K ⟶ (ChainComplex.single₀ A).obj Z)
    [QuasiIso f] (F : A) (hA : ∀ p j,Subsingleton (Ext (K.X p) F (j+1))) (q : ℕ) :
    AddCommGrpCat.of (Ext Z F (q+1)) ≅ cokernel (acyclicChainOpcycleHomPrecompose K F q) := by
  have hK : K.ExactAt (q+1) :=
    (exactAt_iff_of_quasiIsoAt f (q+1)).mpr (ChainComplex.exactAt_succ_single_obj Z q)
  letI : Subsingleton (Ext (K.X q) F 1) := hA q 0
  exact (acyclicResolutionGlobalExtOpcycleAddEquiv K Z f F hA q).toAddCommGrpIso ≪≫
    (acyclicChainOpcycleHomGlobalExtCokernelIso K F q hK).symm
end LinearStudy
