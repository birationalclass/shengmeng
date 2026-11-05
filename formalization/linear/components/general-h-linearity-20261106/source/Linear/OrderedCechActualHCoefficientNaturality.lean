module
public import Linear.OrderedCechActualHPointwiseNaturality
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
attribute [local irreducible] orderedFreeSheafActualHomComplexIso
  topFiniteOrderedCech_actualHigherHIso_of_localAcyclic acyclicResolutionActualCochainExtIso
/-- The SAME existing finite ordered-Cech/native-H comparison is NATURAL
in original sheaf coefficient maps. Actual termwise section maps,native
homologyMap and native H.map are retained;no desired naturality input.
Relative local acyclicity of BOTH coefficients is explicit here. -/
theorem topFiniteOrderedCech_actualHigherHIso_of_localAcyclic_coefficient_naturality
    (X : Scheme.{u}) {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (a : F ⟶ G)
    (hF : ∀ (p : ℕ) (b : OrderedCechIndex ι p) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H.{u}
        ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (b.1 k))).obj F) (j+1)))
    (hG : ∀ (p : ℕ) (b : OrderedCechIndex ι p) (j : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H.{u}
        ((topOpenAbelianSheafRestriction X (∏ᶜ fun k : Fin (p+1) => U (b.1 k))).obj G) (j+1)))
    (n : ℕ) :
    HomologicalComplex.homologyMap (orderedTopAbelianCechCoefficientMap X U a) (n+1) ≫
      (topFiniteOrderedCech_actualHigherHIso_of_localAcyclic X U hU G hG n).hom =
      (topFiniteOrderedCech_actualHigherHIso_of_localAcyclic X U hU F hF n).hom ≫
        (CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) (n+1)).map a := by
  ext x
  exact topFiniteOrderedCech_actualHigherHIso_of_localAcyclic_coefficient_naturality_apply
    X U hU a hF hG n x
end LinearStudy
