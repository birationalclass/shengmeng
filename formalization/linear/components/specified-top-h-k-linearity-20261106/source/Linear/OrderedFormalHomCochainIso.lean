module
public import Linear.OrderedFormalCechFunctoriality
public import Linear.AcyclicChainHomExtension
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v w v' w'
/-- Additive coefficient functors commute with the SAME ordered covariant chains. -/
def orderedCovariantWhiskeringChainIso {X : Scheme.{u}}
    {A : Type w} [Category.{v} A] [Preadditive A]
    {B : Type w'} [Category.{v'} B] [Preadditive B]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (F : FormalCoproduct.{u} X.Opens ⥤ A) (H : A ⥤ B) [H.Additive] :
    (H.mapHomologicalComplex (.down ℕ)).obj (orderedFormalCechComplex F.op U).unop ≅
      (orderedFormalCechComplex (F ⋙ H).op U).unop := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j hij
  have hi : j+1=i := hij
  subst i
  simp only [Iso.refl_hom,Category.id_comp,Category.comp_id,Functor.mapHomologicalComplex_obj_d,HomologicalComplex.unop_d,
    orderedFormalCechComplex_d,orderedFormalCechDifferential,orderedFormalCechCoface,
    unop_sum,unop_zsmul,Functor.op_map,Quiver.Hom.unop_op,Functor.comp_map]
  change (∑ k : Fin (j+2),(-1 : ℤ) ^ (k : ℕ) • H.map (F.map (AlgebraicGeometry.Scheme.Modules.orderedCechFace U j k))) =
    H.map (∑ k : Fin (j+2),(-1 : ℤ) ^ (k : ℕ) • F.map (AlgebraicGeometry.Scheme.Modules.orderedCechFace U j k))
  simp only [H.map_sum,H.map_zsmul]
/-- An ACTUAL source-chain isomorphism induces the actual contravariant Hom-complex isomorphism. -/
def actualHomSourceComplexIso {A : Type w} [Category.{v} A] [Abelian A]
    {K L : ChainComplex A ℕ} (e : K ≅ L) (M : A) :
    chainActualHomCochain K M ≅ chainActualHomCochain L M :=
  ((preadditiveYoneda.obj M).mapHomologicalComplex (.up ℕ)).mapIso
    ((HomologicalComplex.opFunctor A (.down ℕ)).mapIso e.symm.op)
/-- Actual Hom of SAME original ordered free chains commutes with ordered differentials. -/
def orderedFormalActualHomCochainIso {X : Scheme.{u}}
    {A : Type w} [Category.{v} A] [Abelian A]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (F : FormalCoproduct.{u} X.Opens ⥤ A) (M : A) :
    chainActualHomCochain (orderedFormalCechComplex F.op U).unop M ≅
      orderedFormalCechComplex (F.op ⋙ preadditiveYoneda.obj M) U :=
  orderedFormalCechWhiskeringIso U F.op (preadditiveYoneda.obj M)
end LinearStudy
