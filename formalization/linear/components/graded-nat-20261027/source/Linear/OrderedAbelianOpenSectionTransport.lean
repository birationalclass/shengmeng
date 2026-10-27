module
public import Linear.AbelianOpenSectionIsoTransport
public import Linear.OrderedFreeSheafHomComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Actual proof term:transport an actual product restriction square to the
ORIGINAL ordered Cech face. The formal-coproduct face is handled once here,
independently of any graded-ring or native-module implementation. -/
def orderedAbelianOpenSectionComparisonIso_restrict
    {X Y : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (G : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1))
    (U0' U1' : X.Opens) (V0' V1' : Y.Opens)
    (hU0 : (∏ᶜ fun j : Fin (p+1) => U ((t.delete k).1 j))=U0')
    (hU1 : (∏ᶜ fun j : Fin (p+2) => U (t.1 j))=U1')
    (hV0 : (∏ᶜ fun j : Fin (p+1) => V ((t.delete k).1 j))=V0')
    (hV1 : (∏ᶜ fun j : Fin (p+2) => V (t.1 j))=V1')
    (fp : U1' ⟶ U0') (gp : V1' ⟶ V0')
    (e0 : F.obj (op U0') ≅ G.obj (op V0')) (e1 : F.obj (op U1') ≅ G.obj (op V1'))
    (he : e0.hom ≫ G.map gp.op = F.map fp.op ≫ e1.hom) :=
  abelianOpenSectionComparisonIso_restrict F G
    (∏ᶜ fun j : Fin (p+1) => U ((t.delete k).1 j)) U0'
    (∏ᶜ fun j : Fin (p+2) => U (t.1 j)) U1'
    (∏ᶜ fun j : Fin (p+1) => V ((t.delete k).1 j)) V0'
    (∏ᶜ fun j : Fin (p+2) => V (t.1 j)) V1'
    hU0 hU1 hV0 hV1 ((orderedCechFace U p k).φ t) fp ((orderedCechFace V p k).φ t) gp e0 e1 he
end LinearStudy
