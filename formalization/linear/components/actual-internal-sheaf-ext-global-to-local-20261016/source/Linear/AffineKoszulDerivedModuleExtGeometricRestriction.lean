module
public import Linear.KoszulExactTopExtCoefficientRestriction
public import Linear.AffineKoszulGeometricRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
variable (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R)
variable (he : ∀ j : ℕ, 0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)

/-- SAME actual derived MODULE Ext representative followed by its actual
restriction equivalence equals the ORIGINAL N/IN coefficient restriction. -/
theorem koszulExactTopExtCoefficientRepresentative_restriction_square :
    (koszulExactTopExtCoefficientRestrictionEquiv n H he N).toLinearMap.comp
        (koszulExactTopExtCoefficientRepresentativeLinearMap n H he N) =
      koszulTopHomCoefficientRestriction (N := N) n H := by
  apply LinearMap.ext
  intro L
  exact koszulExactTopExtCoefficientRestrictionEquiv_representative n H he N L

/-- CONSTRUCT sheafification of ACTUAL derived MODULE Ext as ACTUAL
original geometric cut coefficient i_*i^*tilde N. This is not an assertion
that derived SHEAF Ext or global sheaf cohomology is already identified. -/
def affineKoszulDerivedModuleExtGeometricIso :
    tilde (ModuleCat.of R
      (Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (n+1))) ≅
      (Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
          ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
              (tilde N)) :=
  (tilde.functor R).mapIso (koszulExactTopExtCoefficientRestrictionEquiv n H he N).toModuleIso ≪≫
    tildeCoefficientQuotientGeometricPullbackPushforwardIso R (Ideal.span (Set.range H)) N

attribute [local irreducible] koszulExactTopExtCoefficientRestrictionEquiv
  tildeCoefficientQuotientGeometricPullbackPushforwardIso

/-- The SAME sheafified actual MODULE Ext representative morphism goes
to ORIGINAL ordered-top evaluation followed by ACTUAL geometric restriction.
This proves the map square, not merely an object comparison. -/
theorem affineKoszulDerivedModuleExtGeometricIso_representative :
    (tilde.functor R).map
        (ModuleCat.ofHom (koszulExactTopExtCoefficientRepresentativeLinearMap n H he N)) ≫
      (affineKoszulDerivedModuleExtGeometricIso R N n H he).hom =
    (tilde.functor R).map
      (ModuleCat.ofHom (koszulTopHomCoefficientEquiv (N := N) n).toLinearMap) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).unit.app
          (tilde N) := by
  simp only [affineKoszulDerivedModuleExtGeometricIso, Iso.trans_hom, Functor.mapIso_hom,
    LinearEquiv.toModuleIso_hom]
  erw [← Category.assoc, ← Functor.map_comp, ← ModuleCat.ofHom_comp,
    koszulExactTopExtCoefficientRepresentative_restriction_square]
  have hm : (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom ≫
      (affineKoszulHomGeometricRestrictionPresentation R N n H).g =
    (tilde.functor R).map
      (ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)) ≫
      (tildeCoefficientQuotientGeometricPullbackPushforwardIso R (Ideal.span (Set.range H)) N).hom := by
    change (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom ≫
      ((affineKoszulHomCoefficientRestrictionPresentation R N n H).g ≫ _) = _
    rw [← Category.assoc,affineKoszulHomCoefficientRestrictionPresentation_restriction]
    simp only [tildeKoszulHomCoefficientRestrictionPresentation,
      tildeCoefficientQuotientGeometricPullbackPushforwardIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  exact hm.symm.trans (affineKoszulHomGeometricRestrictionPresentation_restriction R N n H)

/-- Under SAME actual Hom-term iso, the sheafified ACTUAL derived MODULE
Ext representative is EXACTLY the already proved ORIGINAL actual
internal-Hom Koszul geometric-restriction morphism. -/
theorem affineKoszulDerivedModuleExtGeometricIso_internalHom_restriction :
    (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).inv ≫
      (tilde.functor R).map
        (ModuleCat.ofHom (koszulExactTopExtCoefficientRepresentativeLinearMap n H he N)) ≫
      (affineKoszulDerivedModuleExtGeometricIso R N n H he).hom =
    (affineKoszulHomGeometricRestrictionPresentation R N n H).g := by
  apply (cancel_epi (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom).mp
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact (affineKoszulDerivedModuleExtGeometricIso_representative R N n H he).trans
    (affineKoszulHomGeometricRestrictionPresentation_restriction R N n H).symm

end LinearStudy
