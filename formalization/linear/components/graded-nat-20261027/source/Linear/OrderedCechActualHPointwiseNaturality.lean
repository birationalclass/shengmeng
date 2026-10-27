module
public import Linear.OrderedFreeSheafHomCoefficientNaturality
public import Linear.OrderedCechActualHFactorization
public import Linear.OrderedCechActualHComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option diagnostics true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] orderedFreeSheafActualHomComplexIso
  topFiniteOrderedCech_actualHigherHIso_of_localAcyclic acyclicResolutionActualCochainExtIso
/-- The SAME existing finite ordered-Cech/native-H comparison is NATURAL
in original sheaf coefficient maps. Actual termwise section maps,native
homologyMap and native H.map are retained;no desired naturality input.
Relative local acyclicity of BOTH coefficients is explicit here. -/
theorem topFiniteOrderedCech_actualHigherHIso_of_localAcyclic_coefficient_naturality_apply
    (X : Scheme.{u}) {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (a : F ⟶ G)
    (hF : ∀ (p : ℕ) (b : OrderedCechIndex ι p) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H.{u}
        ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (b.1 k))).obj F) (j+1)))
    (hG : ∀ (p : ℕ) (b : OrderedCechIndex ι p) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H.{u}
        ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (b.1 k))).obj G) (j+1)))
    (n : ℕ) (x : (orderedTopAbelianCechComplex X U F).homology (n+1)) :
    (topFiniteOrderedCech_actualHigherHIso_of_localAcyclic X U hU G hG n).hom
      (HomologicalComplex.homologyMap (orderedTopAbelianCechCoefficientMap X U a) (n+1) x) =
    CategoryTheory.Sheaf.H.map.{u} a (n+1)
      ((topFiniteOrderedCech_actualHigherHIso_of_localAcyclic X U hU F hF n).hom x) := by
  let K := orderedFreeAbelianSheafComplex X U
  let Z := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let f := orderedCechNativeIntegerAugmentation X U
  letI : QuasiIso f := orderedCechNativeIntegerAugmentation_quasiIso X U hU
  have hAF (p j : ℕ) : Subsingleton (Ext.{u} (K.X p) F (j+1)) :=
    orderedFiniteFreeSheafTerm_ext_subsingleton X U F p j (fun b => hF p b j)
  have hAG (p j : ℕ) : Subsingleton (Ext.{u} (K.X p) G (j+1)) :=
    orderedFiniteFreeSheafTerm_ext_subsingleton X U G p j (fun b => hG p b j)
  rw [topFiniteOrderedCech_actualHigherHIso_of_localAcyclic_factorization,
    topFiniteOrderedCech_actualHigherHIso_of_localAcyclic_factorization]
  have h := acyclicResolutionActualCochainExtIso_coefficient_naturality K Z f a hAF hAG
    (orderedFreeSheafActualHomComplexIso X U F) (orderedFreeSheafActualHomComplexIso X U G)
    (orderedTopAbelianCechCoefficientMap X U a)
    (orderedFreeSheafActualHomComplexIso_coefficient_naturality X U a) n
  exact ConcreteCategory.congr_hom h x
end LinearStudy
