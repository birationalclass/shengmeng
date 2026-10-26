module
public import Linear.AffineKoszulInternalHomComplexIso
public import Linear.TildeKoszulNativeHomTopCohomology
public import Linear.AffineKoszulGeometricRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- SAME original whole-complex inverse has SAME original term inverse. -/
theorem affineKoszulInternalHomCochainComplexIso_inv_f (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r j : ℕ) (H : Fin r → R) :
    (affineKoszulInternalHomCochainComplexIso R N r H).inv.f j =
      (affineKoszulInternalHomCochainTermIso R N r j H).inv := rfl

attribute [local irreducible] affineKoszulInternalHomCochainComplexIso
  affineKoszulTermHomCoefficientIso affineKoszulNativeHomCochainTermIso
  tildeCoefficientQuotientGeometricPullbackPushforwardIso

/-- SAME native original restriction after tilde is SAME ACTUAL geometric
restriction under original term iso. No desired comparison square is input. -/
theorem affineKoszulInternalHomCochainTermIso_geometricRestriction
    (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulInternalHomCochainTermIso R N (n+1) (n+1) H).hom ≫
      (affineKoszulHomGeometricRestrictionPresentation R N n H).g =
    (tilde.functor R).map (koszulNativeHomTopRestrictionMorphism R N n H) ≫
      (tildeCoefficientQuotientGeometricPullbackPushforwardIso R (Ideal.span (Set.range H)) N).hom := by
  have hlin : (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom ≫
      (affineKoszulHomGeometricRestrictionPresentation R N n H).g =
    (tilde.functor R).map
      (ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)) ≫
      (tildeCoefficientQuotientGeometricPullbackPushforwardIso R (Ideal.span (Set.range H)) N).hom := by
    change (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom ≫
      ((affineKoszulHomCoefficientRestrictionPresentation R N n H).g ≫ _) = _
    rw [← Category.assoc,affineKoszulHomCoefficientRestrictionPresentation_restriction]
    simp only [tildeKoszulHomCoefficientRestrictionPresentation,
      tildeCoefficientQuotientGeometricPullbackPushforwardIso,Iso.trans_hom,
      Functor.mapIso_hom,Iso.symm_hom,Category.assoc]
  simp only [affineKoszulInternalHomCochainTermIso,Iso.trans_hom,
    Functor.mapIso_hom,koszulNativeHomTopRestrictionMorphism,Functor.map_comp,Category.assoc]
  rw [hlin]

/-- The original inverse term map takes actual native restriction to
EXACTLY original internal-Hom geometric restriction. -/
theorem affineKoszulInternalHomCochainTermIso_inv_geometricRestriction
    (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulInternalHomCochainTermIso R N (n+1) (n+1) H).inv ≫
      (tilde.functor R).map (koszulNativeHomTopRestrictionMorphism R N n H) ≫
      (tildeCoefficientQuotientGeometricPullbackPushforwardIso R (Ideal.span (Set.range H)) N).hom =
    (affineKoszulHomGeometricRestrictionPresentation R N n H).g := by
  apply (cancel_epi (affineKoszulInternalHomCochainTermIso R N (n+1) (n+1) H).hom).mp
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact (affineKoszulInternalHomCochainTermIso_geometricRestriction R N n H).symm

/-- ACTUAL top COHOMOLOGY of ACTUAL original Koszul internal-Hom complex
is ACTUAL i_*i^*tilde N for original cut i:Spec(R/I)->Spec R. N arbitrary;
no exactness/FP/free/flat/invertibility/CM/duality/desired iso premise.
Derived SHEAF Ext and global twisted gluing are separate obligations. -/
def affineKoszulInternalHomTopCohomologyGeometricIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulInternalHomCochainComplex R N (n+1) H).homology (n+1) ≅
      (Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
          ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
              (tilde N)) :=
  HomologicalComplex.homologyMapIso
    (affineKoszulInternalHomCochainComplexIso R N (n+1) H).symm (n+1) ≪≫
      tildeKoszulNativeHomTopCohomologyIso R N n H ≪≫
        tildeCoefficientQuotientGeometricPullbackPushforwardIso R (Ideal.span (Set.range H)) N

/-- Under ACTUAL top cohomology iso,SAME actual cycle maps to SAME
original geometric Koszul restriction;object iso alone is insufficient. -/
theorem affineKoszulInternalHomTopCohomologyGeometricIso_restriction
    (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulInternalHomCochainComplex R N (n+1) H).homologyπ (n+1) ≫
      (affineKoszulInternalHomTopCohomologyGeometricIso R N n H).hom =
    (affineKoszulInternalHomCochainComplex R N (n+1) H).iCycles (n+1) ≫
      (affineKoszulHomGeometricRestrictionPresentation R N n H).g := by
  simp only [affineKoszulInternalHomTopCohomologyGeometricIso,Iso.trans_hom,
    HomologicalComplex.homologyMapIso_hom,Iso.symm_hom,Category.assoc]
  rw [reassoc_of% (HomologicalComplex.homologyπ_naturality
    (affineKoszulInternalHomCochainComplexIso R N (n+1) H).inv (n+1))]
  rw [reassoc_of% (tildeKoszulNativeHomTopCohomologyIso_restriction R N n H)]
  rw [reassoc_of% (HomologicalComplex.cyclesMap_i
    (affineKoszulInternalHomCochainComplexIso R N (n+1) H).inv (n+1))]
  rw [affineKoszulInternalHomCochainComplexIso_inv_f,
    affineKoszulInternalHomCochainTermIso_inv_geometricRestriction]

end LinearStudy
