module
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Scheme
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
/-- Transport actual abelian sections along an equality of their opens. -/
def abelianOpenSectionEqIso {X : Scheme.{u}} (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U V : X.Opens) (h : U=V) : F.obj (op U) ≅ F.obj (op V) :=
  F.mapIso (eqToIso (congrArg op h))
/-- Compare actual intersections via their identified product charts. -/
def abelianOpenSectionComparisonIso {X Y : Scheme.{u}}
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (G : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U U' : X.Opens) (V V' : Y.Opens) (hU : U=U') (hV : V=V')
    (e : F.obj (op U') ≅ G.obj (op V')) : F.obj (op U) ≅ G.obj (op V) :=
  abelianOpenSectionEqIso F U U' hU ≪≫ e ≪≫ (abelianOpenSectionEqIso G V V' hV).symm
/-- Equality transport preserves a proved actual restriction square,including
arbitrary original open-inclusion morphisms.There is no new naturality input
on the transported comparison:it follows from the product-chart square. -/
theorem abelianOpenSectionComparisonIso_restrict {X Y : Scheme.{u}}
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (G : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (U0 U0' U1 U1' : X.Opens) (V0 V0' V1 V1' : Y.Opens)
    (hU0 : U0=U0') (hU1 : U1=U1') (hV0 : V0=V0') (hV1 : V1=V1')
    (f : U1 ⟶ U0) (f' : U1' ⟶ U0') (g : V1 ⟶ V0) (g' : V1' ⟶ V0')
    (e0 : F.obj (op U0') ≅ G.obj (op V0')) (e1 : F.obj (op U1') ≅ G.obj (op V1'))
    (he : e0.hom ≫ G.map g'.op = F.map f'.op ≫ e1.hom) :
    (abelianOpenSectionComparisonIso F G U0 U0' V0 V0' hU0 hV0 e0).hom ≫ G.map g.op =
      F.map f.op ≫ (abelianOpenSectionComparisonIso F G U1 U1' V1 V1' hU1 hV1 e1).hom := by
  subst U0'
  subst U1'
  subst V0'
  subst V1'
  have hf : f'=f := Subsingleton.elim _ _
  have hg : g'=g := Subsingleton.elim _ _
  subst f'
  subst g'
  simpa [abelianOpenSectionComparisonIso,abelianOpenSectionEqIso] using he
end LinearStudy
