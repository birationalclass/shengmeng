module
public import Linear.CochainActualTopCovariantExact
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Linear.OriginalChainAugmentationClassZero
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
variable [HasExt.{w} A] [HasDerivedCategory.{d} A] [EnoughInjectives A]
/-- Relative positive Ext vanishing transports along the ACTUAL original
term identification. This does not assert geometric Serre vanishing. -/
theorem originalChainCovariant_middle_acyclic
    (C : ChainComplex A ℕ) (O : A) (r j : ℕ) (hj : j < r) (q : ℕ)
    (hv : Subsingleton (Ext O (C.X (r-j-1)) q)) :
    Subsingleton (Ext O ((originalChainAsCochain C).X (cochainSourceDegree r j+1)) q) := by
  let e := originalChainAsCochainXIso C (cochainSourceDegree r j+1) (r-j-1) (by
    rw [cochainSourceDegree_eq]
    push_cast
    omega)
  exact ((extFunctorObj O q).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr hv

/-- Surjectivity of the SAME ORIGINAL chain extension represented by the
TOP IDENTITY,with no replacement class or assumed compatibility law. -/
theorem originalChainCovariant_surjective
    (C : ChainComplex A ℕ) {E : A} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (hAbove : IsZero (C.X (r+1))) (O : A)
    (hvan : ∀ j,j < r → ∀ q,0 < q → Subsingleton (Ext O (C.X (r-j-1)) q)) :
    ∀ x : Ext O (C.X r) r,∃ y : O ⟶ E,
      (Ext.mk₀ y).comp (originalChainTopExtClass C r alpha (𝟙 _)
        (hAbove.eq_of_src _ _)) (zero_add r) = x := by
  let K := originalChainAsCochain C
  let alpha' := originalChainAugmentationAsCochain C alpha
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  haveI : K.IsStrictlyLE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyLE (C.extend ComplexShape.embeddingDownNat) 0)
  let psi := originalChainAsCochainXIso C (-(r : ℤ)) r rfl
  have hz : IsZero (K.X (-(r : ℤ)-1)) :=
    hAbove.of_iso (originalChainAsCochainXIso C (-(r : ℤ)-1) (r+1) (by push_cast;omega))
  let c := cochainResolutionTopExtClass K r alpha' (𝟙 _) (hz.eq_of_src _ _)
  have hc : c.comp (Ext.mk₀ psi.hom) (add_zero r) =
      originalChainTopExtClass C r alpha (𝟙 _) (hAbove.eq_of_src _ _) := by
    rw [cochainResolutionTopExtClass_comp_mk₀]
    simp only [originalChainTopExtClass,Category.id_comp,Category.comp_id,psi,K,alpha']
  intro x
  obtain ⟨z,hz'⟩ := cochainActualTopCovariant_surjective K r hr alpha' hz
    (injectiveResolution _) O
    (fun j hj q hq => originalChainCovariant_middle_acyclic C O r j hj q (hvan j hj q hq))
    (x.comp (Ext.mk₀ psi.inv) (add_zero r))
  obtain ⟨y,hy⟩ := (Ext.mk₀_bijective O E).2 z
  refine ⟨y,?_⟩
  have h := congrArg (fun a => a.comp (Ext.mk₀ psi.hom) (add_zero r)) hz'
  rw [Ext.comp_assoc_of_third_deg_zero,hc,
    Ext.comp_assoc_of_third_deg_zero,Ext.mk₀_comp_mk₀,psi.inv_hom_id,Ext.comp_mk₀_id] at h
  rw [hy]
  exact h

/-- The kernel of the SAME original chain connecting map is exactly the
image of its SAME zero augmentation. All relative Ext vanishings remain
explicit. This theorem does not prove geometric Serre vanishing. -/
theorem originalChainCovariant_kernel
    (C : ChainComplex A ℕ) {E : A} (p : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (hAbove : IsZero (C.X (p+2))) (O : A)
    (hvan : ∀ j,j < p → ∀ q,0 < q → Subsingleton (Ext O (C.X (p-j)) q))
    (x : O ⟶ E) :
    (Ext.mk₀ x).comp (originalChainTopExtClass C (p+1) alpha (𝟙 _)
        (hAbove.eq_of_src _ _)) (zero_add _) = 0 ↔
      ∃ z : O ⟶ C.X 0,z ≫ alpha.f 0 = x := by
  let K := originalChainAsCochain C
  let alpha' := originalChainAugmentationAsCochain C alpha
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  haveI : K.IsStrictlyLE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyLE (C.extend ComplexShape.embeddingDownNat) 0)
  let psi := originalChainAsCochainXIso C (-((p+1 : ℕ) : ℤ)) (p+1) rfl
  have hz : IsZero (K.X (-((p+1 : ℕ) : ℤ)-1)) :=
    hAbove.of_iso (originalChainAsCochainXIso C (-((p+1 : ℕ) : ℤ)-1) (p+2) (by push_cast;omega))
  let c := cochainResolutionTopExtClass K (p+1) alpha' (𝟙 _) (hz.eq_of_src _ _)
  have hc : c.comp (Ext.mk₀ psi.hom) (add_zero _) =
      originalChainTopExtClass C (p+1) alpha (𝟙 _) (hAbove.eq_of_src _ _) := by
    rw [cochainResolutionTopExtClass_comp_mk₀]
    simp only [originalChainTopExtClass,Category.id_comp,Category.comp_id,psi,K,alpha']
  have hvan' : ∀ j,j < p → ∀ q,0 < q →
      Subsingleton (Ext O (K.X (cochainSourceDegree (p+1) j+1)) q) := by
    intro j hj q hq
    apply originalChainCovariant_middle_acyclic C O (p+1) j (by omega) q
    simpa only [show p+1-j-1=p-j by omega] using hvan j hj q hq
  have hinj : Function.Injective ((Ext.mk₀ psi.hom).postcomp O (add_zero (p+1))) :=
    ((extFunctorObj O (p+1)).mapIso psi).addCommGroupIsoToAddEquiv.bijective.1
  have hziff : (Ext.mk₀ x).comp c (zero_add _) = 0 ↔
      (Ext.mk₀ x).comp (originalChainTopExtClass C (p+1) alpha (𝟙 _)
        (hAbove.eq_of_src _ _)) (zero_add _) = 0 := by
    constructor
    · intro h
      rw [← hc,← Ext.comp_assoc_of_third_deg_zero,h,Ext.zero_comp]
    · intro h
      apply hinj
      change ((Ext.mk₀ x).comp c (zero_add _)).comp (Ext.mk₀ psi.hom) (add_zero _) =
        (0 : Ext O (K.X (-((p+1 : ℕ) : ℤ))) (p+1)).comp (Ext.mk₀ psi.hom) (add_zero _)
      rw [Ext.comp_assoc_of_third_deg_zero,hc,h,Ext.zero_comp]
  rw [← hziff,cochainActualTopCovariant_kernel K p alpha' hz (injectiveResolution _) O hvan']
  constructor
  · rintro ⟨z,hz'⟩
    obtain ⟨z0,hz0⟩ := (Ext.mk₀_bijective O (K.X 0)).2 z
    refine ⟨z0 ≫ (originalChainAsCochainXIso C 0 0 (by norm_num)).hom,?_⟩
    apply (Ext.mk₀_bijective O E).1
    rw [← hz0,Ext.mk₀_comp_mk₀] at hz'
    simpa only [alpha',originalChainAugmentationAsCochain_f_zero,Ext.mk₀_comp_mk₀,Category.assoc] using hz'
  · rintro ⟨z,hz'⟩
    refine ⟨Ext.mk₀ (z ≫ (originalChainAsCochainXIso C 0 0 (by norm_num)).inv),?_⟩
    simp only [alpha',originalChainAugmentationAsCochain_f_zero,Ext.mk₀_comp_mk₀,
      Category.assoc,Iso.inv_hom_id_assoc,hz']
end LinearStudy
