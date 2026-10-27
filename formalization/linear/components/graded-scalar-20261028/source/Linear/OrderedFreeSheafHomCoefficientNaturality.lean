module
public import Linear.OrderedFormalHomCoefficientNaturality
public import Linear.OrderedFreeSheafHomCoefficientPresheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
/-- Actual ORIGINAL ordered-Cech coefficient morphism,acting termwise
by the original sheaf section morphisms and retaining all signs. -/
def orderedTopAbelianCechCoefficientMap (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (a : F ⟶ G) :
    orderedTopAbelianCechComplex X U F ⟶ orderedTopAbelianCechComplex X U G :=
  (orderedFormalCechCoefficientFunctor U).map
    ((FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).map a.hom)
attribute [local irreducible] orderedFreeSheafActualHomComplexIso orderedFreeSheafHomCoefficientPresheafIso
/-- The presheaf factor is EXACTLY the factor used by the existing
actual ordered free-sheaf Hom/Cech comparison. -/
theorem orderedFreeSheafActualHomComplexIso_factorization
    (X : Scheme.{u}) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    orderedFreeSheafActualHomComplexIso X U F =
      actualHomSourceComplexIso (orderedCovariantWhiskeringChainIso U
        (orderedFreeOpenFormalPresheafFunctor X)
        (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) F ≪≫
      orderedFormalActualHomCochainIso U ((orderedFreeOpenFormalPresheafFunctor X) ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) F ≪≫
      (orderedFormalCechCoefficientFunctor U).mapIso (orderedFreeSheafHomCoefficientPresheafIso X F) := by
  rw [orderedFormalCechCoefficientFunctor_mapIso]
  unfold orderedFreeSheafActualHomComplexIso orderedFreeSheafHomCoefficientPresheafIso
  rfl
/-- The SAME already used actual Hom/Cech comparison commutes with
ORIGINAL termwise section coefficient maps,no transported replacement. -/
theorem orderedFreeSheafActualHomComplexIso_coefficient_naturality
    (X : Scheme.{u}) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (a : F ⟶ G) :
    chainActualHomCochainCoefficientMap (orderedFreeAbelianSheafComplex X U) a ≫
      (orderedFreeSheafActualHomComplexIso X U G).hom =
      (orderedFreeSheafActualHomComplexIso X U F).hom ≫ orderedTopAbelianCechCoefficientMap X U a := by
  let P := orderedFreeOpenFormalPresheafFunctor X
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let T := orderedFormalCechCoefficientFunctor (D:=AddCommGrpCat.{u}) U
  let K := (orderedFormalCechComplex (P ⋙ S).op U).unop
  let e := orderedCovariantWhiskeringChainIso U P S
  have h₁ : CommSq (chainActualHomCochainCoefficientMap (orderedFreeAbelianSheafComplex X U) a)
      (actualHomSourceComplexIso e F).hom (actualHomSourceComplexIso e G).hom
      (chainActualHomCochainCoefficientMap K a) := ⟨actualHomSourceComplexIso_coefficient_naturality e a⟩
  have h₂ : CommSq (chainActualHomCochainCoefficientMap K a)
      (orderedFormalActualHomCochainIso U (P ⋙ S) F).hom
      (orderedFormalActualHomCochainIso U (P ⋙ S) G).hom
      (T.map (Functor.whiskerLeft (P ⋙ S).op (preadditiveYoneda.map a))) :=
    ⟨orderedFormalActualHomCochainIso_coefficient_naturality U (P ⋙ S) a⟩
  have h₃ : CommSq (T.map (Functor.whiskerLeft (P ⋙ S).op (preadditiveYoneda.map a)))
      (T.mapIso (orderedFreeSheafHomCoefficientPresheafIso X F)).hom
      (T.mapIso (orderedFreeSheafHomCoefficientPresheafIso X G)).hom
      (orderedTopAbelianCechCoefficientMap X U a) := by
    constructor
    change T.map _ ≫ T.map _ = T.map _ ≫ T.map _
    simpa only [Functor.map_comp] using
      congrArg T.map (orderedFreeSheafHomCoefficientPresheafIso_coefficient_naturality X a)
  rw [orderedFreeSheafActualHomComplexIso_factorization,orderedFreeSheafActualHomComplexIso_factorization]
  change chainActualHomCochainCoefficientMap (orderedFreeAbelianSheafComplex X U) a ≫
      ((actualHomSourceComplexIso e G).hom ≫
        ((orderedFormalActualHomCochainIso U (P ⋙ S) G).hom ≫
          (T.mapIso (orderedFreeSheafHomCoefficientPresheafIso X G)).hom)) =
    ((actualHomSourceComplexIso e F).hom ≫
      ((orderedFormalActualHomCochainIso U (P ⋙ S) F).hom ≫
        (T.mapIso (orderedFreeSheafHomCoefficientPresheafIso X F)).hom)) ≫
      orderedTopAbelianCechCoefficientMap X U a
  exact (h₁.vert_comp (h₂.vert_comp h₃)).w
end LinearStudy
