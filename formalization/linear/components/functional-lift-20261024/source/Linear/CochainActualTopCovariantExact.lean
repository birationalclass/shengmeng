module
public import Linear.CochainActualRoofCovariantExact
public import Linear.CochainResolutionTopExtNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
/-- The SAME actual top projection is an isomorphism when the preceding
term is zero,by its native universal cokernel property. -/
def cochainActualTopOpcycleIso (K : CochainComplex A ℤ) (r : ℕ)
    (hAbove : IsZero (K.X (-(r : ℤ)-1))) :
    K.X (-(r : ℤ)) ≅ K.opcycles (cochainSourceDegree r 0) := by
  let pi : K.X (-(r : ℤ)) ⟶ K.opcycles (cochainSourceDegree r 0) :=
    K.pOpcycles (cochainSourceDegree r 0)
  haveI : IsIso pi := CokernelCofork.IsColimit.isIso_π
    (CokernelCofork.ofπ pi (K.d_pOpcycles (-(r : ℤ)-1) (cochainSourceDegree r 0)))
    (K.opcyclesIsCokernel (-(r : ℤ)-1) (cochainSourceDegree r 0) (by simp [cochainSourceDegree]))
    (hAbove.eq_of_src _ _)
  exact asIso pi

theorem cochainActualTopOpcycleIso_hom (K : CochainComplex A ℤ) (r : ℕ)
    (hAbove : IsZero (K.X (-(r : ℤ)-1))) :
    (cochainActualTopOpcycleIso K r hAbove).hom = K.pOpcycles (cochainSourceDegree r 0) := rfl

variable [HasExt.{w} A] [HasDerivedCategory.{d} A]
/-- ACTUAL connecting map represented by IDENTITY on the original TOP
TERM is onto. Neither a replacement top coefficient nor a class law is
input;the native top projection iso and coefficient naturality prove it. -/
theorem cochainActualTopCovariant_surjective
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E : A} (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (hAbove : IsZero (K.X (-(r : ℤ)-1)))
    (I : InjectiveResolution (K.opcycles (cochainSourceDegree r 0))) (O : A)
    (hvan : ∀ j,j < r → ∀ q,0 < q →
      Subsingleton (Ext O (K.X (cochainSourceDegree r j+1)) q)) :
    ∀ x : Ext O (K.X (-(r : ℤ))) r,∃ y : Ext O E 0,
      y.comp (cochainResolutionTopExtClass K r alpha (𝟙 _)
        (hAbove.eq_of_src _ _)) (zero_add r) = x := by
  let phi := cochainActualTopOpcycleIso K r hAbove
  let c : Ext E (K.X (-(r : ℤ))) r :=
    cochainResolutionTopExtClass K r alpha (𝟙 _) (hAbove.eq_of_src _ _)
  have hc : c.comp (Ext.mk₀ phi.hom) (add_zero r) =
      cochainResolutionTopExtClass K r alpha (K.pOpcycles (cochainSourceDegree r 0))
        (K.d_pOpcycles (-(r : ℤ)-1) (cochainSourceDegree r 0)) := by
    simpa only [c,phi,cochainActualTopOpcycleIso_hom,Category.id_comp] using
      cochainResolutionTopExtClass_comp_mk₀ K r alpha (𝟙 _) (hAbove.eq_of_src _ _) phi.hom
  have hinj : Function.Injective ((Ext.mk₀ phi.hom).postcomp O (add_zero r)) :=
    ((extFunctorObj O r).mapIso phi).addCommGroupIsoToAddEquiv.bijective.1
  intro x
  obtain ⟨y,hy⟩ := cochainActualRoofCovariant_surjective K r hr alpha I O hvan
    (x.comp (Ext.mk₀ phi.hom) (add_zero r))
  refine ⟨y,?_⟩
  apply hinj
  change (y.comp c (zero_add r)).comp (Ext.mk₀ phi.hom) (add_zero r) =
    x.comp (Ext.mk₀ phi.hom) (add_zero r)
  rw [Ext.comp_assoc_of_third_deg_zero,hc]
  exact hy

/-- Exact kernel/image identity for the SAME original TOP-identity class
and SAME zero augmentation,under explicit relative cohomology vanishings. -/
theorem cochainActualTopCovariant_kernel
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E : A} (p : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (hAbove : IsZero (K.X (-((p+1 : ℕ) : ℤ)-1)))
    (I : InjectiveResolution (K.opcycles (cochainSourceDegree (p+1) 0))) (O : A)
    (hvan : ∀ j,j < p → ∀ q,0 < q →
      Subsingleton (Ext O (K.X (cochainSourceDegree (p+1) j+1)) q))
    (x : Ext O E 0) :
    x.comp (cochainResolutionTopExtClass K (p+1) alpha (𝟙 _)
        (hAbove.eq_of_src _ _)) (zero_add _) = 0 ↔
      ∃ z : Ext O (K.X 0) 0,z.comp
        (Ext.mk₀ (alpha.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom))
          (add_zero 0) = x := by
  let phi := cochainActualTopOpcycleIso K (p+1) hAbove
  let c : Ext E (K.X (-((p+1 : ℕ) : ℤ))) (p+1) :=
    cochainResolutionTopExtClass K (p+1) alpha (𝟙 _) (hAbove.eq_of_src _ _)
  let b : Ext E (K.opcycles (cochainSourceDegree (p+1) 0)) (p+1) :=
    cochainResolutionTopExtClass K (p+1) alpha (K.pOpcycles (cochainSourceDegree (p+1) 0))
      (K.d_pOpcycles (-((p+1 : ℕ) : ℤ)-1) (cochainSourceDegree (p+1) 0))
  have hc : c.comp (Ext.mk₀ phi.hom) (add_zero _) = b := by
    simpa only [c,b,phi,cochainActualTopOpcycleIso_hom,Category.id_comp] using
      cochainResolutionTopExtClass_comp_mk₀ K (p+1) alpha (𝟙 _)
        (hAbove.eq_of_src _ _) phi.hom
  have hinj : Function.Injective ((Ext.mk₀ phi.hom).postcomp O (add_zero (p+1))) :=
    ((extFunctorObj O (p+1)).mapIso phi).addCommGroupIsoToAddEquiv.bijective.1
  have hz : x.comp c (zero_add _) = 0 ↔ x.comp b (zero_add _) = 0 := by
    constructor
    · intro h
      rw [← hc,← Ext.comp_assoc_of_third_deg_zero,h,Ext.zero_comp]
    · intro h
      apply hinj
      change (x.comp c (zero_add _)).comp (Ext.mk₀ phi.hom) (add_zero _) =
        (0 : Ext O (K.X (-((p+1 : ℕ) : ℤ))) (p+1)).comp (Ext.mk₀ phi.hom) (add_zero _)
      rw [Ext.comp_assoc_of_third_deg_zero,hc,h,Ext.zero_comp]
  exact hz.trans (cochainActualRoofCovariant_kernel K p alpha I O hvan x)
end LinearStudy
