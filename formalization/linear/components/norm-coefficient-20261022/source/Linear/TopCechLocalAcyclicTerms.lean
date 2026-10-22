module
public import Linear.TopCechFiniteFreeSheafTerms
public import Linear.TopOpenRestrictionActualCohomology
public import Linear.FiniteCoproductExtAcyclic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace AlgebraicTopology
universe u
/-- Local native-H acyclicity on ORIGINAL intersections DERIVES Ext-acyclicity of
SAME actual free-sheaf Cech terms. F arbitrary;no projectivity or target-H premise. -/
theorem topCechFiniteFreeSheafTerm_ext_subsingleton (X : TopCat.{u})
    {ι : Type u} [Finite ι] (U : ι → Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (p j : ℕ)
    (h : ∀ i : Fin (p+1) → ι, Subsingleton (CategoryTheory.Sheaf.H.{u}
      ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (i k))).obj F) (j+1))) :
    Subsingleton (Ext.{u}
      (((alternatingFaceMapComplex _).obj (topCechFreeAbelianAugmented X U).left).X p) F (j+1)) := by
  let V : (Fin (p+1) → ι) → Opens X := fun i => ∏ᶜ fun k : Fin (p+1) => U (i k)
  have hO (i : Fin (p+1) → ι) :
      Subsingleton (Ext.{u} ((topOpenFreeAbelianSheafFunctor X).obj (V i)) F (j+1)) :=
    topOpenFreeSheafExt_subsingleton_of_actualH X (V i) F (j+1) (h i)
  exact ext_subsingleton_of_source_iso (topCechFiniteFreeSheafTermIso X U p).symm (j+1)
    (finiteCoproduct_ext_subsingleton (fun i : Fin (p+1) → ι =>
      (topOpenFreeAbelianSheafFunctor X).obj (V i)) F (j+1) hO)
end LinearStudy
