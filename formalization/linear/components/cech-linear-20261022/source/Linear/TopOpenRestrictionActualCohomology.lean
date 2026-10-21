module
public import Linear.TopOpenRestrictionPointedSource
public import Linear.PointedExactFunctorExtMapIsIso
public import Linear.TopAbelianSheafFlasqueCohomology
public import Linear.TopAbelianSheafInjectiveFlasque
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
universe u
/-- ACTUAL free-open Ext canonically computes ACTUAL native H on the SAME open,
in EVERY degree and for ANY abelian SHEAF. Restriction of injectives is only claimed
flasque/acyclic,not injective. No Cech/affine/Serre/duality hypothesis. -/
def topOpenFreeSheafExtActualHAddEquiv (X : TopCat.{u}) (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Ext.{u} ((topOpenFreeAbelianSheafFunctor X).obj U) F n ≃+
      CategoryTheory.Sheaf.H.{u} ((topOpenAbelianSheafRestriction X U).obj F) n :=
  AddEquiv.ofBijective
    (pointedExactFunctorExtMap (topOpenAbelianSheafRestriction X U)
      (topOpenRestrictionIntegerPoint X U) F n)
    (pointedExactFunctorExtMap_bijective (topOpenAbelianSheafRestriction X U)
      (topOpenRestrictionIntegerPoint X U)
      (fun M => topOpenRestrictionPointedExt_zero_bijective X U M)
      (fun I _ j => topAbelianSheaf_flasque_higherCohomology_vanish _ _
        (topOpenAbelianSheafRestriction_isFlasque X U I
          (topAbelianSheaf_injective_isFlasque X I)) j) F n)
/-- Local native-H vanishing therefore DERIVES free-open Ext vanishing. -/
theorem topOpenFreeSheafExt_subsingleton_of_actualH (X : TopCat.{u}) (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (h : Subsingleton (CategoryTheory.Sheaf.H.{u} ((topOpenAbelianSheafRestriction X U).obj F) n)) :
    Subsingleton (Ext.{u} ((topOpenFreeAbelianSheafFunctor X).obj U) F n) := by
  letI := h
  exact (topOpenFreeSheafExtActualHAddEquiv X U F n).injective.subsingleton
end LinearStudy
