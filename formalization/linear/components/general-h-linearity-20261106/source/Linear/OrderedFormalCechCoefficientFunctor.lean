module
public import Linear.OrderedFormalCechFunctoriality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u v w
variable {X : Scheme.{u}} {D : Type w} [Category.{v} D] [Preadditive D]
variable {ι : Type u} [LinearOrder ι]
/-- SAME original ordered alternating Cech complex,functorially in the
actual coefficient presheaf. No transported or desired comparison map. -/
def orderedFormalCechCoefficientFunctor (U : ι → X.Opens) :
    ((FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D) ⥤ CochainComplex D ℕ where
  obj F := orderedFormalCechComplex F U
  map a := CochainComplex.ofHom
    (fun n => a.app (op (orderedCechFormalObject U n))) (fun n => by
      simp only [orderedFormalCechComplex_d,orderedFormalCechDifferential,
        sum_comp,comp_sum,zsmul_comp,comp_zsmul]
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
        (a.naturality (orderedCechFace U n k).op).symm)
  map_id F := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  map_comp a b := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
/-- Its mapIso is EXACTLY the previously used ordered Cech isomorphism. -/
theorem orderedFormalCechCoefficientFunctor_mapIso (U : ι → X.Opens)
    {F G : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D} (e : F ≅ G) :
    (orderedFormalCechCoefficientFunctor U).mapIso e = orderedFormalCechComplexIso U e := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext n
  rfl
end LinearStudy
