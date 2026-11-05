module
public import Linear.OrderedCrossSpaceCechCoefficientNaturality
public import Linear.OrderedAbelianOpenSectionTransport
public import Linear.OrderedCrossSpaceAbelianCechIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Actual coefficient naturality for the original ordered complexes built
from product charts. All intersection transports and signed faces are supplied. -/
def orderedCrossSpaceAbelianCechComplexIso_of_productCharts_coefficient
    {X Y : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (F F' : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (G G' : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (P : ∀ p : ℕ,OrderedCechIndex ι p → X.Opens)
    (Q : ∀ p : ℕ,OrderedCechIndex ι p → Y.Opens)
    (hP : ∀ p t,(∏ᶜ fun j : Fin (p+1) => U (t.1 j))=P p t)
    (hQ : ∀ p t,(∏ᶜ fun j : Fin (p+1) => V (t.1 j))=Q p t)
    (rP : ∀ (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)),P (p+1) t ⟶ P p (t.delete k))
    (rQ : ∀ (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)),Q (p+1) t ⟶ Q p (t.delete k))
    (e : ∀ p t,F.obj (op (P p t)) ≅ G.obj (op (Q p t)))
    (he : ∀ (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)),
      (e p (t.delete k)).hom ≫ G.map (rQ p k t).op = F.map (rP p k t).op ≫ (e (p+1) t).hom)
    (e' : ∀ p t,F'.obj (op (P p t)) ≅ G'.obj (op (Q p t)))
    (he' : ∀ (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)),
      (e' p (t.delete k)).hom ≫ G'.map (rQ p k t).op = F'.map (rP p k t).op ≫ (e' (p+1) t).hom)
    (a : F ⟶ F') (b : G ⟶ G')
    (ha : ∀ p t,(e p t).hom ≫ b.app (op (Q p t)) = a.app (op (P p t)) ≫ (e' p t).hom) :=
  orderedCrossSpaceAbelianCechComplexIso_coefficient F F' G G' U V
    (fun p t => abelianOpenSectionComparisonIso F G _ (P p t) _ (Q p t) (hP p t) (hQ p t) (e p t))
    (fun p k t => orderedAbelianOpenSectionComparisonIso_restrict F G U V p k t
      (P p (t.delete k)) (P (p+1) t) (Q p (t.delete k)) (Q (p+1) t)
      (hP p (t.delete k)) (hP (p+1) t) (hQ p (t.delete k)) (hQ (p+1) t)
      (rP p k t) (rQ p k t) (e p (t.delete k)) (e (p+1) t) (he p k t))
    (fun p t => abelianOpenSectionComparisonIso F' G' _ (P p t) _ (Q p t) (hP p t) (hQ p t) (e' p t))
    (fun p k t => orderedAbelianOpenSectionComparisonIso_restrict F' G' U V p k t
      (P p (t.delete k)) (P (p+1) t) (Q p (t.delete k)) (Q (p+1) t)
      (hP p (t.delete k)) (hP (p+1) t) (hQ p (t.delete k)) (hQ (p+1) t)
      (rP p k t) (rQ p k t) (e' p (t.delete k)) (e' (p+1) t) (he' p k t))
    a b (fun p t => abelianOpenSectionComparisonIso_coefficient F F' G G' _ _ _ _
      (hP p t) (hQ p t) (e p t) (e' p t) a b (ha p t))
end LinearStudy
