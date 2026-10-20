module
public import Linear.TopCechLocalAcyclicTerms
public import Linear.AcyclicResolutionExtVanishing
public import Linear.TopCechFreeSheafHomComplex
public import Linear.AlternatingHomOppositeComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace AlgebraicTopology
universe u
/-- ACTUAL local-acyclic finite-cover criterion: zero positive native FULL Cech homology
DERIVES zero positive native SHEAF H for the SAME arbitrary coefficient sheaf.
Local acyclicity is on actual original opens,with no desired Cech/H comparison premise.
This is a vanishing criterion,not yet an all-cohomology isomorphism or an ordered-Cech bridge. -/
theorem topFiniteCech_actualHigherH_vanish_of_localAcyclic (X : TopCat.{u})
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : (⊤ : Opens X) ≤ iSup U)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hC : ∀ p, ((cechComplexFunctor U).obj F.obj).ExactAt (p+1))
    (hlocal : ∀ (p : ℕ) (i : Fin (p+1) → ι) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H.{u}
        ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (i k))).obj F) (j+1)))
    (n : ℕ) : Subsingleton (CategoryTheory.Sheaf.H.{u} F (n+1)) := by
  let S := (topCechFreeAbelianAugmented X U).left
  let K := (alternatingFaceMapComplex _).obj S
  let Z := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let f : K ⟶ (ChainComplex.single₀ _).obj Z := topCechNativeIntegerAugmentation X U
  letI : QuasiIso f := topCechNativeIntegerAugmentation_quasiIso X U hU
  let e : chainActualHomCochain K F ≅ (cechComplexFunctor U).obj F.obj :=
    alternatingHomCochainIso S (preadditiveYoneda.obj F) ≪≫ topCechFreeSheafHomComplexIso X U F
  have hH (p : ℕ) : (chainActualHomCochain K F).ExactAt (p+1) := (hC p).of_iso e.symm
  exact acyclicResolution_ext_subsingleton K Z f F hH
    (fun p j => topCechFiniteFreeSheafTerm_ext_subsingleton X U F p j (fun i => hlocal p i j)) n
end LinearStudy
