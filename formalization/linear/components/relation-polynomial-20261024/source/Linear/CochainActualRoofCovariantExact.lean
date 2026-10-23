module
public import Linear.CochainOpcycleSignedExact
public import Linear.CochainOpcycleSignedRoof
public import Linear.CochainResolutionAugmentationZero
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
variable [HasExt.{w} A] [HasDerivedCategory.{d} A]
/-- Actual original quotient projections respect actual index transport. -/
theorem cochain_pOpcycles_index_transport (K : CochainComplex A ℤ) (j : ℤ) (h : j=0) :
    K.pOpcycles j ≫ eqToHom (congrArg (fun i => K.opcycles i) h) =
      (K.XIsoOfEq h).hom ≫ K.pOpcycles 0 := by
  subst j
  simp
/-- The covariant connecting map of the SAME original resolution ROOF
is ONTO under explicit positive relative Ext vanishings of its SAME
actual terms. This uses the proved native signed-class identification,
not a replacement extension or an assumed connecting-map law. -/
theorem cochainActualRoofCovariant_surjective
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E : A} (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (I : InjectiveResolution (K.opcycles (cochainSourceDegree r 0))) (O : A)
    (hvan : ∀ j,j < r → ∀ q,0 < q →
      Subsingleton (Ext O (K.X (cochainSourceDegree r j+1)) q)) :
    ∀ x : Ext O (K.opcycles (cochainSourceDegree r 0)) r,
      ∃ y : Ext O E 0,
        y.comp (cochainResolutionTopExtClass K r alpha
          (K.pOpcycles (cochainSourceDegree r 0))
          (K.d_pOpcycles (-(r : ℤ)-1) (cochainSourceDegree r 0))) (zero_add r) = x := by
  let T := cochainSourceTerminalMap r (cochainAugmentationOpcycle alpha)
  let c : Ext E (K.opcycles (cochainSourceDegree r 0)) r :=
    cochainResolutionTopExtClass K r alpha (K.pOpcycles (cochainSourceDegree r 0))
      (K.d_pOpcycles (-(r : ℤ)-1) (cochainSourceDegree r 0))
  have hc : cochainOpcycleSignedExtension K r alpha r le_rfl =
      (Ext.mk₀ T).comp c (zero_add r) := by
    simpa only [T,c,cochainSourceDegree] using
      cochainOpcycleSignedExtension_eq_actual_roof K r hr alpha I
  intro x
  obtain ⟨z,hz⟩ := cochainOpcycleSignedExtension_surjective K r alpha O hvan x
  refine ⟨z.comp (Ext.mk₀ T) (add_zero 0),?_⟩
  change (z.comp (Ext.mk₀ T) (add_zero 0)).comp c (zero_add r) = x
  rw [Ext.comp_assoc z (Ext.mk₀ T) c (add_zero 0) (zero_add r) (zero_add r),← hc]
  exact hz

/-- Kernel of the SAME actual original roof connecting map is EXACTLY
the image of SAME original degree-zero augmentation. Native terminal
iso and actual index/projection compatibility are DERIVED. Relative
positive Ext vanishings are explicit,not a global-projectivity claim. -/
theorem cochainActualRoofCovariant_kernel
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E : A} (p : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (I : InjectiveResolution (K.opcycles (cochainSourceDegree (p+1) 0))) (O : A)
    (hvan : ∀ j,j < p → ∀ q,0 < q →
      Subsingleton (Ext O (K.X (cochainSourceDegree (p+1) j+1)) q))
    (x : Ext O E 0) :
    x.comp (cochainResolutionTopExtClass K (p+1) alpha
        (K.pOpcycles (cochainSourceDegree (p+1) 0))
        (K.d_pOpcycles (-((p+1 : ℕ) : ℤ)-1) (cochainSourceDegree (p+1) 0))) (zero_add _) = 0 ↔
      ∃ z : Ext O (K.X 0) 0,z.comp
        (Ext.mk₀ (alpha.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom))
          (add_zero 0) = x := by
  let T := cochainSourceTerminalMap (p+1) (cochainAugmentationOpcycle alpha)
  haveI : IsIso (cochainAugmentationOpcycle alpha) := cochainAugmentationOpcycle_isIso alpha
  haveI : IsIso T := cochainSourceTerminalMap_isIso (p+1) _
  let e := asIso T
  let c : Ext E (K.opcycles (cochainSourceDegree (p+1) 0)) (p+1) :=
    cochainResolutionTopExtClass K (p+1) alpha
      (K.pOpcycles (cochainSourceDegree (p+1) 0))
      (K.d_pOpcycles (-((p+1 : ℕ) : ℤ)-1) (cochainSourceDegree (p+1) 0))
  have hc : cochainOpcycleSignedExtension K (p+1) alpha (p+1) le_rfl =
      (Ext.mk₀ e.hom).comp c (zero_add _) := by
    simpa only [e,T,c,cochainSourceDegree,asIso_hom] using
      cochainOpcycleSignedExtension_eq_actual_roof K (p+1) (by omega) alpha I
  change x.comp c (zero_add _) = 0 ↔ _
  constructor
  · intro hx
    let x' := x.comp (Ext.mk₀ e.inv) (add_zero 0)
    have hcancel : x'.comp (Ext.mk₀ e.hom) (add_zero 0) = x := by
      dsimp only [x']
      rw [Ext.comp_assoc x (Ext.mk₀ e.inv) (Ext.mk₀ e.hom) (add_zero 0) (add_zero 0) (add_zero 0),
        Ext.mk₀_comp_mk₀,e.inv_hom_id,Ext.comp_mk₀_id]
    have hx' : x'.comp (cochainOpcycleSignedExtension K (p+1) alpha (p+1) le_rfl) (zero_add _) = 0 := by
      rw [hc,← Ext.comp_assoc x' (Ext.mk₀ e.hom) c (add_zero 0) (zero_add _) (zero_add _),hcancel]
      exact hx
    obtain ⟨z,hz⟩ := (cochainOpcycleSignedExtension_kernel K (p+1) alpha O p le_rfl hvan x').mp hx'
    let j := cochainSourceDegree (p+1) p+1
    have hj : j=0 := by dsimp only [j];rw [cochainSourceDegree_eq];omega
    let phi := K.XIsoOfEq hj
    let a0 := alpha.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom
    have hbridge : K.pOpcycles j ≫ e.hom = phi.hom ≫ a0 := by
      change K.pOpcycles j ≫
          (eqToHom (congrArg (fun i => K.opcycles i) hj) ≫ cochainAugmentationOpcycle alpha) = _
      rw [← Category.assoc,cochain_pOpcycles_index_transport K j hj,Category.assoc,
        cochainAugmentationOpcycle_projection]
    refine ⟨z.comp (Ext.mk₀ phi.hom) (add_zero 0),?_⟩
    change (z.comp (Ext.mk₀ phi.hom) (add_zero 0)).comp (Ext.mk₀ a0) (add_zero 0) = x
    calc
      (z.comp (Ext.mk₀ phi.hom) (add_zero 0)).comp (Ext.mk₀ a0) (add_zero 0) =
          z.comp (Ext.mk₀ (phi.hom ≫ a0)) (add_zero 0) := by
        rw [Ext.comp_assoc_of_third_deg_zero,Ext.mk₀_comp_mk₀]
      _ = z.comp (Ext.mk₀ (K.pOpcycles j ≫ e.hom)) (add_zero 0) := by rw [hbridge]
      _ = (z.comp (Ext.mk₀ (K.pOpcycles j)) (add_zero 0)).comp (Ext.mk₀ e.hom) (add_zero 0) := by
        rw [Ext.comp_assoc_of_third_deg_zero,Ext.mk₀_comp_mk₀]
      _ = x'.comp (Ext.mk₀ e.hom) (add_zero 0) := by rw [hz]
      _ = x := hcancel
  · rintro ⟨z,rfl⟩
    have hkill : (Ext.mk₀ (alpha.f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom)).comp c (zero_add _) = 0 := by
      dsimp only [c,cochainResolutionTopExtClass]
      exact cochainResolutionExtClass_augmentation_precomp_zero K (p+1) (by omega) alpha _
    rw [Ext.comp_assoc z _ c (add_zero 0) (zero_add _) (zero_add _),hkill,Ext.comp_zero]
end LinearStudy
