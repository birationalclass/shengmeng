module
public import Linear.NativeExtUniverseTransport
public import Linear.ChainResolutionTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w₁ w₂ d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w₁} A] [HasExt.{w₂} A] [HasDerivedCategory.{d} A]
/-- Native universe transport retains EXACTLY the SAME original derived roof class,augmentation and top functional. -/
theorem nativeExtUniverseEquiv_originalChainTopExtClass
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    nativeExtUniverseEquiv.{u,v,w₁,w₂} E N r
      (originalChainTopExtClass.{w₁,d,v,u} C r alpha a ha : Ext.{w₁} E N r) =
      (originalChainTopExtClass.{w₂,d,v,u} C r alpha a ha : Ext.{w₂} E N r) := by
  apply Ext.homEquiv.injective
  change (nativeExtUniverseEquiv.{u,v,w₁,w₂} E N r
      (originalChainTopExtClass.{w₁,d,v,u} C r alpha a ha : Ext.{w₁} E N r)).hom =
    (originalChainTopExtClass.{w₂,d,v,u} C r alpha a ha : Ext.{w₂} E N r).hom
  rw [nativeExtUniverseEquiv_hom]
  simp only [originalChainTopExtClass,cochainResolutionTopExtClass,cochainResolutionExtClass_hom]
end LinearStudy
