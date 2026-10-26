module
public import Linear.AffineKoszulDerivedModuleExtGeometricRestriction
public import Linear.AffineKoszulInternalHomTopCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R)
variable (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)

/-- Compare associated ACTUAL MODULE Ext with cohomology of the ACTUAL
internal-Hom Koszul complex using two already proved geometric-cut isos.
This is not an identification with derived SHEAF Ext. -/
def affineKoszulActualModuleExtInternalHomTopIso :
    tilde (ModuleCat.of R
      (Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (n+1))) ≅
      (affineKoszulInternalHomCochainComplex R N (n+1) H).homology (n+1) :=
  affineKoszulDerivedModuleExtGeometricIso R N n H he ≪≫
    (affineKoszulInternalHomTopCohomologyGeometricIso R N n H).symm

/-- The ACTUAL map from original internal-Hom cycles to the associated
MODULE Ext class,using the SAME actual term iso and representative map. -/
def affineKoszulActualInternalHomCyclesToModuleExt :
    (affineKoszulInternalHomCochainComplex R N (n+1) H).cycles (n+1) ⟶
      tilde (ModuleCat.of R
        (Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (n+1))) :=
  (affineKoszulInternalHomCochainComplex R N (n+1) H).iCycles (n+1) ≫
    (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).inv ≫
      (tilde.functor R).map
        (ModuleCat.ofHom (koszulExactTopExtCoefficientRepresentativeLinearMap n H he N))

/-- The SAME actual cycle maps to its actual internal-Hom homology class.
This verifies a morphism square,not only an object iso. No desired square,
internal derived SHEAF Ext identification or Ext inverse is a premise. -/
theorem affineKoszulActualModuleExtInternalHomTopIso_cycles :
    affineKoszulActualInternalHomCyclesToModuleExt R N n H he ≫
      (affineKoszulActualModuleExtInternalHomTopIso R N n H he).hom =
        (affineKoszulInternalHomCochainComplex R N (n+1) H).homologyπ (n+1) := by
  have combine : ∀ {S X Y E Z G : (Spec R).Modules}
      (i : S ⟶ X) (a : X ⟶ Y) (b : Y ⟶ E) (pi : S ⟶ Z)
      (eE : E ≅ G) (eH : Z ≅ G) (g : X ⟶ G),
      a ≫ b ≫ eE.hom = g → pi ≫ eH.hom = i ≫ g →
      (i ≫ a ≫ b) ≫ (eE ≪≫ eH.symm).hom = pi := by
    intro S X Y E Z G i a b pi eE eH g hg hp
    apply (cancel_mono eH.hom).mp
    simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [hg]
    exact hp.symm
  exact combine
    ((affineKoszulInternalHomCochainComplex R N (n+1) H).iCycles (n+1))
    (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).inv
    ((tilde.functor R).map
      (ModuleCat.ofHom (koszulExactTopExtCoefficientRepresentativeLinearMap n H he N)))
    ((affineKoszulInternalHomCochainComplex R N (n+1) H).homologyπ (n+1))
    (affineKoszulDerivedModuleExtGeometricIso R N n H he)
    (affineKoszulInternalHomTopCohomologyGeometricIso R N n H)
    (affineKoszulHomGeometricRestrictionPresentation R N n H).g
    (affineKoszulDerivedModuleExtGeometricIso_internalHom_restriction R N n H he)
    (affineKoszulInternalHomTopCohomologyGeometricIso_restriction R N n H)

end LinearStudy
