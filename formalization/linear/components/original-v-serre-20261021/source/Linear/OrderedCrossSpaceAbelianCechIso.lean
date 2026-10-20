module
public import Linear.OrderedFormalCechComplex
public import Mathlib.Algebra.Category.Grp.Limits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Projection formula for each SAME ordered coface with arbitrary actual
abelian section coefficients.It reuses the native product evaluation. -/
@[reassoc] theorem orderedAbelianCechCoface_comp_pi {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → X.Opens)
    (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)) :
    orderedFormalCechCoface ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).obj F) U p k ≫
      Pi.π (fun j : OrderedCechIndex ι (p+1) => F.obj (op (∏ᶜ fun l : Fin (p+2) => U (j.1 l)))) t =
      Pi.π (fun j : OrderedCechIndex ι p => F.obj (op (∏ᶜ fun l : Fin (p+1) => U (j.1 l)))) (t.delete k) ≫
        F.map ((orderedCechFace U p k).φ t).op := by
  change (Pi.lift (fun j : OrderedCechIndex ι (p+1) =>
    Pi.π (fun l : OrderedCechIndex ι p => F.obj (op (∏ᶜ fun m : Fin (p+1) => U (l.1 m)))) (j.delete k) ≫
      F.map ((orderedCechFace U p k).φ j).op)) ≫ _ = _
  exact Pi.lift_comp_π _ t
/-- Intersection isomorphisms respecting EVERY original deletion face induce
an isomorphism of the SAME ordered Cech complexes on two spaces.The integer
alternating signs and original index family are retained at every degree. -/
def orderedCrossSpaceAbelianCechComplexIso {X Y : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (G : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (e : ∀ (p : ℕ) (t : OrderedCechIndex ι p),
      F.obj (op (∏ᶜ fun l : Fin (p+1) => U (t.1 l))) ≅
        G.obj (op (∏ᶜ fun l : Fin (p+1) => V (t.1 l))))
    (he : ∀ (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)),
      (e p (t.delete k)).hom ≫ G.map ((orderedCechFace V p k).φ t).op =
        F.map ((orderedCechFace U p k).φ t).op ≫ (e (p+1) t).hom) :
    orderedFormalCechComplex ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).obj F) U ≅
      orderedFormalCechComplex ((FormalCoproduct.evalOp Y.Opens AddCommGrpCat.{u}).obj G) V := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p => Pi.mapIso (e p)) ?_
  intro i j hij
  have hj : i+1=j := hij
  subst j
  simp only [orderedFormalCechComplex_d,orderedFormalCechDifferential]
  rw [CategoryTheory.Preadditive.comp_sum,CategoryTheory.Preadditive.sum_comp]
  simp only [CategoryTheory.Preadditive.zsmul_comp,CategoryTheory.Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
  apply Pi.hom_ext
  intro t
  let A (p : ℕ) (j : OrderedCechIndex ι p) := F.obj (op (∏ᶜ fun l : Fin (p+1) => U (j.1 l)))
  let B (p : ℕ) (j : OrderedCechIndex ι p) := G.obj (op (∏ᶜ fun l : Fin (p+1) => V (j.1 l)))
  let cF := orderedFormalCechCoface ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).obj F) U i k
  let cG := orderedFormalCechCoface ((FormalCoproduct.evalOp Y.Opens AddCommGrpCat.{u}).obj G) V i k
  change (Pi.mapIso (e i)).hom ≫ cG ≫ Pi.π (B (i+1)) t =
    cF ≫ (Pi.mapIso (e (i+1))).hom ≫ Pi.π (B (i+1)) t
  calc
    (Pi.mapIso (e i)).hom ≫ cG ≫ Pi.π (B (i+1)) t =
        (Pi.mapIso (e i)).hom ≫ Pi.π (B i) (t.delete k) ≫ G.map ((orderedCechFace V i k).φ t).op := by
      exact congrArg (fun f => (Pi.mapIso (e i)).hom ≫ f) (orderedAbelianCechCoface_comp_pi G V i k t)
    _ = Pi.π (A i) (t.delete k) ≫ (e i (t.delete k)).hom ≫ G.map ((orderedCechFace V i k).φ t).op := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ G.map ((orderedCechFace V i k).φ t).op) (Pi.mapIso_hom_π (e i) (t.delete k))
    _ = Pi.π (A i) (t.delete k) ≫ F.map ((orderedCechFace U i k).φ t).op ≫ (e (i+1) t).hom := by
      exact congrArg (fun f => Pi.π (A i) (t.delete k) ≫ f) (he i k t)
    _ = cF ≫ Pi.π (A (i+1)) t ≫ (e (i+1) t).hom := by
      simpa only [Category.assoc] using (congrArg (fun f => f ≫ (e (i+1) t).hom)
        (orderedAbelianCechCoface_comp_pi F U i k t)).symm
    _ = cF ≫ (Pi.mapIso (e (i+1))).hom ≫ Pi.π (B (i+1)) t := by
      exact congrArg (fun f => cF ≫ f) (Pi.mapIso_hom_π (e (i+1)) t).symm
end LinearStudy
