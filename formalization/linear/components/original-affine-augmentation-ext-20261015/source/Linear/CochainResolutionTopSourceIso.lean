module
public import Linear.CochainResolutionSourceIso
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
open CochainComplex.HomComplex
universe w d v u
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- Transport the SAME degree-minus-r functional and actual augmentation
along a constructed source-complex isomorphism. Its actual Ext class
is unchanged,with the original cocycle condition derived by commutation. -/
theorem cochainResolutionTopExtClass_sourceIso
    (K L : CochainComplex A ℤ) (gamma : K ≅ L) {E M : A} (r : ℕ)
    (alpha : L ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (a : L.X (-(r:ℤ)) ⟶ M) (ha : L.d (-(r:ℤ)-1) (-(r:ℤ)) ≫ a = 0) :
    cochainResolutionTopExtClass K r (gamma.hom ≫ alpha)
      (gamma.hom.f (-(r:ℤ)) ≫ a) (by simp [← gamma.hom.comm_assoc,ha]) =
        cochainResolutionTopExtClass L r alpha a ha := by
  simp only [cochainResolutionTopExtClass]
  rw [Cocycle.toSingleMk_precomp _ _ _ _ ha gamma.hom,
    Cocycle.equivHomShift_symm_precomp]
  simpa only [ShiftedHom.mk₀_comp] using cochainResolutionExtClass_sourceIso K L gamma r alpha
    (Cocycle.equivHomShift.symm (Cocycle.toSingleMk a (by simp) (-(r:ℤ)-1) (by omega) ha))

end LinearStudy