module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
open CochainComplex.HomComplex
universe w w' v u
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{w'} A]

/-- Build an ACTUAL derived Ext class from a quasi-isomorphic augmented
cochain complex and an actual shifted cocycle map. No projectivity of
individual resolution terms is assumed. Original applications must
construct the actual resolution,quasiiso and cocycle rather than supply
the desired Ext class or its boundary/support identity. -/
def cochainResolutionExtClass (K : CochainComplex A ℤ) {E M : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (beta : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj M) (r : ℤ)) :
    Ext.{w} E M r :=
  Ext.homEquiv.symm
    ((ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app E ≫
      inv (DerivedCategory.Q.map alpha))).comp
        ((ShiftedHom.map beta DerivedCategory.Q).comp
          (.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ A 0).inv.app M))
            (zero_add _)) (add_zero _))

/-- The constructed class is the specified ACTUAL derived roof,with the
original augmentation inverted and the original cocycle retained. -/
theorem cochainResolutionExtClass_hom (K : CochainComplex A ℤ) {E M : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (beta : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj M) (r : ℤ)) :
    (cochainResolutionExtClass K r alpha beta).hom =
      (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app E ≫
        inv (DerivedCategory.Q.map alpha))).comp
          ((ShiftedHom.map beta DerivedCategory.Q).comp
            (.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ A 0).inv.app M))
              (zero_add _)) (add_zero _) :=
  Ext.homEquiv.apply_symm_apply _

/-- Use the native to-single cocycle constructor on a top functional of
an ACTUAL cochain resolution. Only the incoming-differential vanishing
is explicit here;bounded original Koszul applications must derive it. -/
def cochainResolutionTopExtClass (K : CochainComplex A ℤ) {E M : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (f : K.X (-(r : ℤ)) ⟶ M)
    (hf : K.d (-(r : ℤ)-1) (-(r : ℤ)) ≫ f = 0) : Ext.{w} E M r :=
  cochainResolutionExtClass K r alpha (Cocycle.equivHomShift.symm
    (Cocycle.toSingleMk f (by simp) (-(r : ℤ)-1) (by omega) hf))

end LinearStudy
