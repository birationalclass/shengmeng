module
public import Linear.OrderedCrossSpaceCechEndomorphism
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Equality transport preserves the actual coefficient square between TWO
original coefficient sheaves on their SAME original intersection opens. -/
theorem abelianOpenSectionComparisonIso_coefficient {X Y : Scheme.{u}}
    (F F' : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (G G' : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U U' : X.Opens) (V V' : Y.Opens) (hU : U=U') (hV : V=V')
    (e : F.obj (op U') ≅ G.obj (op V')) (e' : F'.obj (op U') ≅ G'.obj (op V'))
    (a : F ⟶ F') (b : G ⟶ G')
    (he : e.hom ≫ b.app (op V') = a.app (op U') ≫ e'.hom) :
    (abelianOpenSectionComparisonIso F G U U' V V' hU hV e).hom ≫ b.app (op V) =
      a.app (op U) ≫ (abelianOpenSectionComparisonIso F' G' U U' V V' hU hV e').hom := by
  subst U'
  subst V'
  simpa [abelianOpenSectionComparisonIso,abelianOpenSectionEqIso] using he
/-- Coefficient naturality on EACH original intersection gives naturality
for the SAME TWO cross-space ordered Cech complex comparisons. All product
objects,faces,signs and actual original coefficient maps are retained. -/
theorem orderedCrossSpaceAbelianCechComplexIso_coefficient
    {X Y : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (F F' : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (G G' : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (e : ∀ (p : ℕ) (t : OrderedCechIndex ι p),
      F.obj (op (∏ᶜ fun l : Fin (p+1) => U (t.1 l))) ≅
        G.obj (op (∏ᶜ fun l : Fin (p+1) => V (t.1 l))))
    (he : ∀ (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)),
      (e p (t.delete k)).hom ≫ G.map ((orderedCechFace V p k).φ t).op =
        F.map ((orderedCechFace U p k).φ t).op ≫ (e (p+1) t).hom)
    (e' : ∀ (p : ℕ) (t : OrderedCechIndex ι p),
      F'.obj (op (∏ᶜ fun l : Fin (p+1) => U (t.1 l))) ≅
        G'.obj (op (∏ᶜ fun l : Fin (p+1) => V (t.1 l))))
    (he' : ∀ (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)),
      (e' p (t.delete k)).hom ≫ G'.map ((orderedCechFace V p k).φ t).op =
        F'.map ((orderedCechFace U p k).φ t).op ≫ (e' (p+1) t).hom)
    (a : F ⟶ F') (b : G ⟶ G')
    (ha : ∀ (p : ℕ) (t : OrderedCechIndex ι p),
      (e p t).hom ≫ b.app (op (∏ᶜ fun l : Fin (p+1) => V (t.1 l))) =
        a.app (op (∏ᶜ fun l : Fin (p+1) => U (t.1 l))) ≫ (e' p t).hom) :
    (orderedCrossSpaceAbelianCechComplexIso F G U V e he).hom ≫
      (orderedFormalCechCoefficientFunctor V).map
        ((FormalCoproduct.evalOp.{u} Y.Opens AddCommGrpCat.{u}).map b) =
    (orderedFormalCechCoefficientFunctor U).map
        ((FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).map a) ≫
      (orderedCrossSpaceAbelianCechComplexIso F' G' U V e' he').hom := by
  apply HomologicalComplex.Hom.ext
  funext p
  change CategoryTheory.Limits.Pi.map (fun t : OrderedCechIndex ι p => (e p t).hom) ≫
      CategoryTheory.Limits.Pi.map (fun t : OrderedCechIndex ι p => b.app (op (∏ᶜ fun l : Fin (p+1) => V (t.1 l)))) =
    CategoryTheory.Limits.Pi.map (fun t : OrderedCechIndex ι p => a.app (op (∏ᶜ fun l : Fin (p+1) => U (t.1 l)))) ≫
      CategoryTheory.Limits.Pi.map (fun t : OrderedCechIndex ι p => (e' p t).hom)
  rw [CategoryTheory.Limits.Pi.map_comp_map,CategoryTheory.Limits.Pi.map_comp_map]
  congr 1
  funext t
  exact ha p t
end LinearStudy
