module
public import Linear.CochainResolutionExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- Use PROVED equal actual augmentations/cocycles through their dependent
quasi-isomorphism instances. No equality of Ext classes is a premise. -/
theorem cochainResolutionExtClass_congr
    (K : CochainComplex A ℤ) {E M : A} (r : ℕ)
    (alpha alpha' : K ⟶ (CochainComplex.singleFunctor A 0).obj E)
    [QuasiIso alpha] [QuasiIso alpha'] (ha : alpha = alpha')
    (beta beta' : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj M) (r:ℤ))
    (hb : beta = beta') :
    cochainResolutionExtClass K r alpha beta =
      cochainResolutionExtClass K r alpha' beta' := by
  subst alpha'
  subst beta'
  rfl

end LinearStudy
