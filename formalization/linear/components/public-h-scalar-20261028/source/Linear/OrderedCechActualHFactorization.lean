module
public import Linear.AcyclicResolutionCochainComparisonIso
public import Linear.OrderedCechActualHComparison
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
/-- A SMALL exact factorization of the EXISTING geometric Cech/native-H
comparison through the SAME named acyclic-resolution construction.
This proves equality,not a replacement cohomology model. -/
theorem topFiniteOrderedCech_actualHigherHIso_of_localAcyclic_factorization
    (X : Scheme.{u}) {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : ∀ (p : ℕ) (b : OrderedCechIndex ι p) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H.{u}
        ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (b.1 k))).obj F) (j+1)))
    (n : ℕ) :
    topFiniteOrderedCech_actualHigherHIso_of_localAcyclic X U hU F hF n =
      (letI : QuasiIso (orderedCechNativeIntegerAugmentation X U) :=
          orderedCechNativeIntegerAugmentation_quasiIso X U hU
       acyclicResolutionActualCochainExtIso
        (orderedFreeAbelianSheafComplex X U)
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))
        (orderedCechNativeIntegerAugmentation X U) F
        (fun p j => orderedFiniteFreeSheafTerm_ext_subsingleton X U F p j (fun b => hF p b j))
        (orderedFreeSheafActualHomComplexIso X U F) n) := by
  rfl
end LinearStudy
