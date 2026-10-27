module
public import Linear.OrderedFreeSheafHomComplex
public import Linear.TopCechLocalAcyclicTerms
public import Linear.AcyclicResolutionExtVanishing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Actual ordered free-SHEAF terms are the finite coproduct of the SAME original
free-open sheaves on their ORIGINAL ordered intersections. -/
def orderedFiniteFreeSheafTermIso (X : Scheme.{u}) {ι : Type u} [LinearOrder ι] [Finite ι]
    (U : ι → X.Opens) (n : ℕ) : (orderedFreeAbelianSheafComplex X U).X n ≅
      ∐ (fun a : OrderedCechIndex ι n => (topOpenFreeAbelianSheafFunctor X).obj
        (∏ᶜ fun k : Fin (n+1) => U (a.1 k))) := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  letI : HasColimitsOfShape (Discrete (OrderedCechIndex ι n)) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape
  letI : HasColimitsOfShape (Discrete (OrderedCechIndex ι n))
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let K := topOpenFreeAbelianPresheafFunctor X
  change S.obj (∐ (fun a : OrderedCechIndex ι n => K.obj
    (∏ᶜ fun k : Fin (n+1) => U (a.1 k)))) ≅ _
  exact PreservesCoproduct.iso S _
/-- Local native-H acyclicity on ORIGINAL ordered intersections DERIVES acyclicity
of the SAME actual ordered free-SHEAF terms. -/
theorem orderedFiniteFreeSheafTerm_ext_subsingleton (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (p j : ℕ)
    (h : ∀ a : OrderedCechIndex ι p,Subsingleton (CategoryTheory.Sheaf.H.{u}
      ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (a.1 k))).obj F) (j+1))) :
    Subsingleton (Ext.{u} ((orderedFreeAbelianSheafComplex X U).X p) F (j+1)) := by
  letI : Finite (OrderedCechIndex ι p) := by unfold OrderedCechIndex; infer_instance
  have hO (a : OrderedCechIndex ι p) : Subsingleton (Ext.{u}
      ((topOpenFreeAbelianSheafFunctor X).obj (∏ᶜ fun k : Fin (p+1) => U (a.1 k))) F (j+1)) :=
    topOpenFreeSheafExt_subsingleton_of_actualH X _ F (j+1) (h a)
  exact ext_subsingleton_of_source_iso (orderedFiniteFreeSheafTermIso X U p).symm (j+1)
    (finiteCoproduct_ext_subsingleton (fun a : OrderedCechIndex ι p =>
      (topOpenFreeAbelianSheafFunctor X).obj (∏ᶜ fun k : Fin (p+1) => U (a.1 k))) F (j+1) hO)
/-- ACTUAL ordered-Cech local-to-global vanishing criterion,for the SAME native
SHEAF H.No ordered/full comparison or desired native-H vanishing premise is assumed. -/
theorem topFiniteOrderedCech_actualHigherH_vanish_of_localAcyclic (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hC : ∀ p,(orderedTopAbelianCechComplex X U F).ExactAt (p+1))
    (hlocal : ∀ (p : ℕ) (a : OrderedCechIndex ι p) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H.{u}
        ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (a.1 k))).obj F) (j+1)))
    (n : ℕ) : Subsingleton (CategoryTheory.Sheaf.H.{u} F (n+1)) := by
  let K := orderedFreeAbelianSheafComplex X U
  let Z := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let f : K ⟶ (ChainComplex.single₀ _).obj Z := orderedCechNativeIntegerAugmentation X U
  letI : QuasiIso f := orderedCechNativeIntegerAugmentation_quasiIso X U hU
  let e := orderedFreeSheafActualHomComplexIso X U F
  have hH (p : ℕ) : (chainActualHomCochain K F).ExactAt (p+1) := (hC p).of_iso e.symm
  exact acyclicResolution_ext_subsingleton K Z f F hH
    (fun p j => orderedFiniteFreeSheafTerm_ext_subsingleton X U F p j (fun a => hlocal p a j)) n
end LinearStudy
