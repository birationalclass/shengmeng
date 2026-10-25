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

/-- Transport the ACTUAL augmentation and cocycle along a constructed
source-complex isomorphism. The resulting derived roof is unchanged.
No projectivity or desired Ext-class equality is a premise. -/
theorem cochainResolutionExtClass_sourceIso
    (K L : CochainComplex A ℤ) (gamma : K ≅ L) {E M : A} (r : ℕ)
    (alpha : L ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (beta : ShiftedHom L ((CochainComplex.singleFunctor A 0).obj M) (r:ℤ)) :
    cochainResolutionExtClass K r (gamma.hom ≫ alpha)
      ((ShiftedHom.mk₀ 0 rfl gamma.hom).comp beta (add_zero _)) =
        cochainResolutionExtClass L r alpha beta := by
  apply Ext.ext
  simp only [cochainResolutionExtClass_hom,ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀,
    ShiftedHom.map,Functor.map_comp,IsIso.inv_comp,Category.assoc]
  simp

end LinearStudy