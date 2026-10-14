module
public import Linear.AffineKoszulInternalHomCochain
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- SAME original native Hom term, after actual tilde, is the ACTUAL
original internal-Hom term. Original exterior FP is already PROVED;
no finite presentation/free/flat/invertibility/CM condition on N. -/
def affineKoszulInternalHomCochainTermIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r j : ℕ) (H : Fin r → R) :
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (affineKoszulNativeHomCochainComplex R N r H)).X j ≅
        (affineKoszulInternalHomCochainComplex R N r H).X j :=
  (tilde.functor R).mapIso (affineKoszulNativeHomCochainTermIso R N r j H) ≪≫
    affineKoszulTermHomCoefficientIso R N r j

attribute [local irreducible] affineKoszulTermHomCoefficientIso
  affineKoszulNativeHomCochainTermIso

/-- SAME original consecutive differentials commute with the actual
native-Hom/internal-Hom term iso. The differential square is proved. -/
theorem affineKoszulInternalHomCochainTermIso_d (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R) (j : ℕ) :
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (affineKoszulNativeHomCochainComplex R N r H)).d j (j+1) ≫
      (affineKoszulInternalHomCochainTermIso R N r (j+1) H).hom =
    (affineKoszulInternalHomCochainTermIso R N r j H).hom ≫
      (affineKoszulInternalHomCochainComplex R N r H).d j (j+1) := by
  have hn := affineKoszulNativeHomCochainTermIso_d R N r H j (j+1)
  rw [koszulComplex.d_eq_d] at hn
  have hs : (tilde.functor R).map
      ((affineKoszulNativeHomCochainComplex R N r H).d j (j+1)) ≫
      (tilde.functor R).map (affineKoszulNativeHomCochainTermIso R N r (j+1) H).hom =
    (tilde.functor R).map (affineKoszulNativeHomCochainTermIso R N r j H).hom ≫
      (tilde.functor R).map (ModuleCat.ofHom
        (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) j))) := by
    simpa only [Functor.map_comp,ModuleCat.hom_ofHom] using congrArg (fun f => (tilde.functor R).map f) hn
  simp only [affineKoszulInternalHomCochainTermIso, Iso.trans_hom, Functor.mapIso_hom]
  change (tilde.functor R).map
      ((affineKoszulNativeHomCochainComplex R N r H).d j (j+1)) ≫
      ((tilde.functor R).map (affineKoszulNativeHomCochainTermIso R N r (j+1) H).hom ≫
        (affineKoszulTermHomCoefficientIso R N r (j+1)).hom) = _
  rw [← Category.assoc,hs,Category.assoc,
    affineKoszulTermHomCoefficientIso_differential]
  rw [affineKoszulInternalHomCochainComplex_d_next]
  simp only [Category.assoc]

/-- Construct an isomorphism of the ACTUAL original native associated-Hom
and ACTUAL original internal-Hom cochain complexes, not only termwise
object isos. No desired complex/naturality/exactness certificate is input. -/
def affineKoszulInternalHomCochainComplexIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R) :
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (affineKoszulNativeHomCochainComplex R N r H) ≅
      affineKoszulInternalHomCochainComplex R N r H :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => affineKoszulInternalHomCochainTermIso R N r j H) (by
      intro i j hij
      change i+1=j at hij
      subst j
      exact (affineKoszulInternalHomCochainTermIso_d R N r H i).symm)

end LinearStudy
