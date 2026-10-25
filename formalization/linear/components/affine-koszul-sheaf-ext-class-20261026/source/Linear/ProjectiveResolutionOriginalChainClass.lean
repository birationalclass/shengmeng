module
public import Linear.ChainResolutionTopExtClass
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe v u w d
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- When the SAME actual chain resolution is projective,its constructed
roof class is native ProjectiveResolution.extMk of the SAME functional.
This uses native mathlib extMk_hom;it does not make sheaf terms projective. -/
theorem originalChainTopExtClass_eq_projectiveResolution_extMk
    {E M : A} (P : ProjectiveResolution E) (r : ℕ)
    (a : P.complex.X r ⟶ M) (ha : P.complex.d (r+1) r ≫ a = 0) :
    originalChainTopExtClass P.complex r P.π a ha = P.extMk a (r+1) rfl ha := by
  apply Ext.homEquiv.injective
  simp only [originalChainTopExtClass,cochainResolutionTopExtClass,
    cochainResolutionExtClass_hom,ProjectiveResolution.extMk_hom]
  simp [originalChainAsCochain,originalChainAugmentationAsCochain,originalChainAsCochainXIso,
    ProjectiveResolution.cochainComplex,ProjectiveResolution.π',ProjectiveResolution.cochainComplexXIso,
    Int.natCast_add,Int.natCast_one,neg_add_rev,sub_eq_add_neg,add_comm]

end LinearStudy
