module
public import Linear.CochainResolutionExactFunctorCompatibility
public import Linear.ChainResolutionTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe v u v' u' wA wB dA dB
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]

/-- The ACTUAL original top functional as the native shifted cochain
cocycle,with the same degree conversion and original differential. -/
def originalChainTopShiftedCocycle (C : ChainComplex A ℕ) {M : A} (r : ℕ)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    ShiftedHom (originalChainAsCochain C) ((CochainComplex.singleFunctor A 0).obj M) (r:ℤ) := by
  refine Cocycle.equivHomShift.symm (Cocycle.toSingleMk
    ((originalChainAsCochainXIso C (-(r:ℤ)) r rfl).hom ≫ a)
    (by simp) (-(r:ℤ)-1) (by omega) ?_)
  rw [originalChainAsCochain_d C (-(r:ℤ)-1) (-(r:ℤ)) (r+1) r (by omega) rfl]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,ha,comp_zero]

variable [HasExt.{wA} A] [HasDerivedCategory.{dA} A]
variable [HasExt.{wB} B] [HasDerivedCategory.{dB} B]
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The original actual class uses exactly this SAME native cocycle. -/
theorem originalChainTopExtClass_eq_cochain (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    letI := originalChainAugmentationAsCochain_quasiIso C alpha
    originalChainTopExtClass C r alpha a ha =
      cochainResolutionExtClass (originalChainAsCochain C) r
        (originalChainAugmentationAsCochain C alpha) (originalChainTopShiftedCocycle C r a ha) := rfl

/-- Construct the ACTUAL mapped-complex roof of the SAME original chain
resolution,without a new source equivalence or desired class identity. -/
def originalChainMappedTopExtClass (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) : Ext.{wB} (F.obj E) (F.obj M) r := by
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  exact mappedCochainResolutionExtClass F (originalChainAsCochain C) r
    (originalChainAugmentationAsCochain C alpha) (originalChainTopShiftedCocycle C r a ha)

/-- Native exact-functor action sends the SAME original class to its
ACTUAL mapped-complex roof. This permits real open restriction next. -/
theorem originalChainTopExtClass_mapExactFunctor (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    (originalChainTopExtClass C r alpha a ha).mapExactFunctor F =
      originalChainMappedTopExtClass F C r alpha a ha := by
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  rw [originalChainTopExtClass_eq_cochain]
  exact cochainResolutionExtClass_mapExactFunctor F (originalChainAsCochain C) r
    (originalChainAugmentationAsCochain C alpha) (originalChainTopShiftedCocycle C r a ha)

end LinearStudy
