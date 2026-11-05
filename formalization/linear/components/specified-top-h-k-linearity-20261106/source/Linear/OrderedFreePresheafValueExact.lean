module
public import Linear.OrderedFreePresheafValueHomCochain
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
open scoped ZeroObject
/-- For a FINITE original family,every positive actual Hom cochain cocycle over V
is a boundary,for EVERY abelian coefficient group. -/
theorem orderedFreePresheafValue_actualHom_positive_exact (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (V : X.Opens)
    (M : AddCommGrpCat.{u}) (p : ℕ) :
    (chainActualHomCochain (orderedFreePresheafValueChain X U V) M).ExactAt (p+1) := by
  let K := orderedFreePresheafValueChain X U V
  let H := chainActualHomCochain K M
  apply (HomologicalComplex.exactAt_iff' H p (p+1) (p+2) (by simp) (by simp)).mpr
  apply (ShortComplex.ab_exact_iff _).mpr
  intro z hz
  change K.d (p+2) (p+1) ≫ z = 0 at hz
  have hs : ∀ a,orderedConstantCechDifferential (p+1)
      (orderedFreeValueHomCoefficients X U V M (p+1) z) a = 0 := by
    intro a
    rw [← orderedFreeValueHomCoefficients_d,hz,map_zero]
    rfl
  obtain ⟨t,ht⟩ := orderedConstantCech_finite_exists_boundary p
    (orderedFreeValueHomCoefficients X U V M (p+1) z) hs
  refine ⟨(orderedFreeValueHomCoefficients X U V M p).symm t,?_⟩
  change K.d (p+1) p ≫ (orderedFreeValueHomCoefficients X U V M p).symm t = z
  apply (orderedFreeValueHomCoefficients X U V M (p+1)).injective
  funext a
  rw [orderedFreeValueHomCoefficients_d,AddEquiv.apply_symm_apply]
  exact ht a
/-- The SAME finite ordered free-presheaf chain evaluated at ANY actual open is
positive exact;no cover assumption or cohomology-vanishing input is used. -/
theorem orderedFreePresheafValueChain_positive_exact (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (V : X.Opens) (p : ℕ) :
    (orderedFreePresheafValueChain X U V).ExactAt (p+1) :=
  chain_exactAt_of_all_actualHom_exactAt _ p
    (fun M => orderedFreePresheafValue_actualHom_positive_exact X U V M p)
/-- Positive exactness holds in ACTUAL abelian PRESHEAVES,reflected from all actual
open evaluations.No identification of the degree-zero target is claimed here. -/
theorem orderedFreeAbelianPresheafComplex_positive_exact (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (p : ℕ) :
    (orderedFreeAbelianPresheafComplex X U).ExactAt (p+1) := by
  let K := orderedFreeAbelianPresheafComplex X U
  let Z := (ChainComplex.single₀ (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})).obj 0
  let f : K ⟶ Z := 0
  have hZ : Z.ExactAt (p+1) := ChainComplex.exactAt_succ_single_obj _ p
  apply (quasiIsoAt_iff_exactAt' f (p+1) hZ).mp
  apply (HomologicalComplex.quasiIsoAt_iff_evaluation f (p+1)).mpr
  intro V
  let E := ((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj V).mapHomologicalComplex (.down ℕ)
  have hK : (E.obj K).ExactAt (p+1) := by
    change (orderedFreePresheafValueChain X U V.unop).ExactAt (p+1)
    exact orderedFreePresheafValueChain_positive_exact X U V.unop p
  have hZ' : (E.obj Z).ExactAt (p+1) := by
    apply HomologicalComplex.ExactAt.of_isZero
    exact ((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj V).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 _ (p+1) (by omega))
  exact (quasiIsoAt_iff_exactAt (E.map f) (p+1) hK).mpr hZ'
end LinearStudy
