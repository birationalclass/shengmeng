module
public import Linear.CochainResolutionIteratedSourceBoundary
public import Linear.ChainResolutionTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
attribute [local instance] originalChainAugmentationAsCochain_quasiIso
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- ORIGINAL ordered chain top functional is closed on SAME n-to-minus-n source. -/
theorem originalChainTopFunctionalCochain_closed (C : ChainComplex A ℕ) {N : A}
    (r : ℕ) (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    (originalChainAsCochain C).d (-(r : ℤ)-1) (-(r : ℤ)) ≫
      ((originalChainAsCochainXIso C (-(r : ℤ)) r rfl).hom ≫ a) = 0 := by
  rw [originalChainAsCochain_d C (-(r : ℤ)-1) (-(r : ℤ)) (r+1) r (by omega) rfl]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,ha,comp_zero]

/-- Descend SAME ORIGINAL top functional through its ACTUAL source quotient. -/
def originalChainTopOpcycleFunctional (C : ChainComplex A ℕ) {N : A}
    (r : ℕ) (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :=
  cochainTopOpcycleFunctional (originalChainAsCochain C) r
    ((originalChainAsCochainXIso C (-(r : ℤ)) r rfl).hom ≫ a)
    (originalChainTopFunctionalCochain_closed C r a ha)

/-- In EVERY positive original rank,the SAME ORIGINAL epsilon is computed
by ACTUAL native source boundaries from ORIGINAL top functional. The
canonical quotient identification is derived,not assumed. -/
theorem originalChainTopExtClass_iteratedSourceBoundary
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) (I : InjectiveResolution N) :
    cochainOpcycleIteratedBoundary (originalChainAsCochain C) r
      (originalChainAugmentationAsCochain C alpha) r le_rfl
      (Ext.mk₀ (originalChainTopOpcycleFunctional C r a ha)) =
      (Ext.mk₀ (cochainSourceTerminalMap r
        (cochainAugmentationOpcycle (originalChainAugmentationAsCochain C alpha)))).comp
        (originalChainTopExtClass C r alpha a ha) (zero_add r) := by
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  haveI : (originalChainAsCochain C).IsStrictlyLE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyLE (C.extend ComplexShape.embeddingDownNat) 0)
  simpa only [originalChainTopOpcycleFunctional,originalChainTopExtClass] using
    cochainResolutionTopExtClass_iteratedSourceBoundary (originalChainAsCochain C) r hr
      (originalChainAugmentationAsCochain C alpha)
      ((originalChainAsCochainXIso C (-(r : ℤ)) r rfl).hom ≫ a)
      (originalChainTopFunctionalCochain_closed C r a ha) I

end LinearStudy
