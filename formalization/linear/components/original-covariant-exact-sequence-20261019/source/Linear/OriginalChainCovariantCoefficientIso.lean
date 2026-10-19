module
public import Linear.OriginalChainCovariantExact
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
/-- Onto for the SAME original top-frame class,by proved coefficient
naturality and the actual chosen top-term isomorphism. -/
theorem originalChainCovariantCoefficientIso_surjective
    (C : ChainComplex A ℕ) {E M : A} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M) (O : A)
    (hvan : ∀ j,j < r → ∀ q,0 < q → Subsingleton (Ext O (C.X (r-j-1)) q)) :
    ∀ x : Ext O M r,∃ y : O ⟶ E,
      (Ext.mk₀ y).comp (originalChainTopExtClass C r alpha phi.hom
        (hAbove.eq_of_src _ _)) (zero_add r) = x := by
  intro x
  obtain ⟨y,hy⟩ := originalChainCovariant_surjective C r hr alpha hAbove O hvan
    (x.comp (Ext.mk₀ phi.inv) (add_zero r))
  refine ⟨y,?_⟩
  have hc : (originalChainTopExtClass C r alpha (𝟙 _) (hAbove.eq_of_src _ _)).comp
      (Ext.mk₀ phi.hom) (add_zero r) =
      originalChainTopExtClass C r alpha phi.hom (hAbove.eq_of_src _ _) := by
    simpa only [Category.id_comp] using
      originalChainTopExtClass_comp_mk₀ C r alpha (𝟙 _) (hAbove.eq_of_src _ _) phi.hom
  have h := congrArg (fun a => a.comp (Ext.mk₀ phi.hom) (add_zero r)) hy
  rw [Ext.comp_assoc_of_third_deg_zero,hc,
    Ext.comp_assoc_of_third_deg_zero,Ext.mk₀_comp_mk₀,
    phi.inv_hom_id,Ext.comp_mk₀_id] at h
  exact h
/-- Exact kernel/image for the SAME original top-frame class. Vanishing
of the actual middle relative Ext groups is an explicit separate input. -/
theorem originalChainCovariantCoefficientIso_kernel
    (C : ChainComplex A ℕ) {E M : A} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M) (O : A)
    (hvan : ∀ j,j < r → ∀ q,0 < q → Subsingleton (Ext O (C.X (r-j-1)) q))
    (x : O ⟶ E) :
    (Ext.mk₀ x).comp (originalChainTopExtClass C r alpha phi.hom
        (hAbove.eq_of_src _ _)) (zero_add r) = 0 ↔
      ∃ z : O ⟶ C.X 0,z ≫ alpha.f 0 = x := by
  cases r with
  | zero => omega
  | succ p =>
    let c := originalChainTopExtClass C (p+1) alpha (𝟙 _) (hAbove.eq_of_src _ _)
    have hc : c.comp (Ext.mk₀ phi.hom) (add_zero _) =
        originalChainTopExtClass C (p+1) alpha phi.hom (hAbove.eq_of_src _ _) := by
      simpa only [c,Category.id_comp] using
        originalChainTopExtClass_comp_mk₀ C (p+1) alpha (𝟙 _) (hAbove.eq_of_src _ _) phi.hom
    have hinj : Function.Injective ((Ext.mk₀ phi.hom).postcomp O (add_zero (p+1))) :=
      ((extFunctorObj O (p+1)).mapIso phi).addCommGroupIsoToAddEquiv.bijective.1
    have hziff : (Ext.mk₀ x).comp c (zero_add _) = 0 ↔
        (Ext.mk₀ x).comp (originalChainTopExtClass C (p+1) alpha phi.hom
          (hAbove.eq_of_src _ _)) (zero_add _) = 0 := by
      constructor
      · intro h
        rw [← hc,← Ext.comp_assoc_of_third_deg_zero,h,Ext.zero_comp]
      · intro h
        apply hinj
        change ((Ext.mk₀ x).comp c (zero_add _)).comp (Ext.mk₀ phi.hom) (add_zero _) =
          (0 : Ext O (C.X (p+1)) (p+1)).comp (Ext.mk₀ phi.hom) (add_zero _)
        rw [Ext.comp_assoc_of_third_deg_zero,hc,h,Ext.zero_comp]
    rw [← hziff]
    exact originalChainCovariant_kernel C p alpha hAbove O
      (fun j hj q hq => by simpa only [show p+1-j-1=p-j by omega] using hvan j (by omega) q hq) x
end LinearStudy
