module
public import Linear.AcyclicResolutionGlobalExtHomology
public import Linear.OrderedCechNativeHVanishing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Actual locally acyclic finite ordered Cech cover computes ACTUAL native
positive SHEAF H,not only a vanishing criterion. Same ordered free resolution,
same native integer sheaf,same coefficient and original alternating differential.
Local acyclicity is explicit here and DERIVED in affine-QC applications.
No general comparison or desired native-H result is assumed. -/
def topFiniteOrderedCech_actualHigherHIso_of_localAcyclic (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hlocal : ∀ (p : ℕ) (a : OrderedCechIndex ι p) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H.{u}
        ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (a.1 k))).obj F) (j+1)))
    (n : ℕ) : (orderedTopAbelianCechComplex X U F).homology (n+1) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} F (n+1)) := by
  let K := orderedFreeAbelianSheafComplex X U
  let Z := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let f : K ⟶ (ChainComplex.single₀ _).obj Z := orderedCechNativeIntegerAugmentation X U
  letI : QuasiIso f := orderedCechNativeIntegerAugmentation_quasiIso X U hU
  let e := orderedFreeSheafActualHomComplexIso X U F
  have hA (p j : ℕ) : Subsingleton (Ext.{u} (K.X p) F (j+1)) :=
    orderedFiniteFreeSheafTerm_ext_subsingleton X U F p j (fun a => hlocal p a j)
  exact (HomologicalComplex.homologyFunctor _ _ (n+1)).mapIso e.symm ≪≫
    (acyclicResolutionGlobalExtActualHomologyIso K Z f F hA n).symm
end LinearStudy
