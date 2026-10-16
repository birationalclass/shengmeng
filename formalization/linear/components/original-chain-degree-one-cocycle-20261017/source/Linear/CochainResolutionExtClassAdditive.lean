module
public import Linear.CochainResolutionExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe w d v u
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- Negating the SAME actual cocycle negates its SAME derived roof class. -/
theorem cochainResolutionExtClass_neg
    (K : CochainComplex A ℤ) {E M : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (beta : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj M) (r:ℤ)) :
    cochainResolutionExtClass K r alpha (-beta) =
      -cochainResolutionExtClass K r alpha beta := by
  apply Ext.ext
  rw [Ext.neg_hom]
  simp [cochainResolutionExtClass_hom,ShiftedHom.map]

end LinearStudy
