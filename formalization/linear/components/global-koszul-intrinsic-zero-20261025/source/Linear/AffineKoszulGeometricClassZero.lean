module
public import Linear.AffineKoszulGeometricRestriction
public import Linear.SchemeModuleHomUnitCurry
public import Linear.SchemeModuleGeometricPullbackZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (p : ℕ)
/-- The ACTUAL ordered-top coefficient section of an actual sheaf
functional. It uses the already proved original finite-presentation Hom
comparison and ORIGINAL ordered exterior generator;N is arbitrary. -/
def affineKoszulTopFunctionalSection
    (a : tilde (ModuleCat.of R (⋀[R]^(p+1) (Fin (p+1) → R))) ⟶ tilde N) :
    SheafOfModules.unit (Spec R).ringCatSheaf ⟶ tilde N :=
  (schemeModuleHomUnitAddEquiv _ (tilde N)).symm a ≫
    (affineKoszulTermHomCoefficientIso R N (p+1) (p+1)).inv ≫
      (tilde.functor R).map
        (ModuleCat.ofHom (koszulTopHomCoefficientEquiv (N := N) p).toLinearMap)
/-- The SAME actual class representative equals actual geometric
restriction of its ordered coefficient section to the ORIGINAL scheme
cut Spec(R/(H)). No radicalization,flatness or coefficient frame premise. -/
theorem affineKoszulGeometricClass_eq_restriction (H : Fin (p+1) → R)
    (a : tilde (ModuleCat.of R (⋀[R]^(p+1) (Fin (p+1) → R))) ⟶ tilde N) :
    (schemeModuleHomUnitAddEquiv _ (tilde N)).symm a ≫
        (affineKoszulHomGeometricRestrictionPresentation R N p H).g =
      affineKoszulTopFunctionalSection R N p a ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).unit.app
            (tilde N) := by
  have hg : (affineKoszulHomGeometricRestrictionPresentation R N p H).g =
      (affineKoszulTermHomCoefficientIso R N (p+1) (p+1)).inv ≫
        (tilde.functor R).map
          (ModuleCat.ofHom (koszulTopHomCoefficientEquiv (N := N) p).toLinearMap) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).unit.app
            (tilde N) := by
    apply (cancel_epi (affineKoszulTermHomCoefficientIso R N (p+1) (p+1)).hom).mp
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using
      affineKoszulHomGeometricRestrictionPresentation_restriction R N p H
  rw [hg]
  simp only [affineKoszulTopFunctionalSection,Category.assoc]
/-- An actual original Koszul class representative vanishes EXACTLY
when the actual ordered coefficient section vanishes after sheaf pullback
to the SAME ORIGINAL nonreduced cut. No faithful-pullback assumption. -/
theorem affineKoszulGeometricClass_zero_iff_pullback (H : Fin (p+1) → R)
    (a : tilde (ModuleCat.of R (⋀[R]^(p+1) (Fin (p+1) → R))) ⟶ tilde N) :
    (schemeModuleHomUnitAddEquiv _ (tilde N)).symm a ≫
        (affineKoszulHomGeometricRestrictionPresentation R N p H).g = 0 ↔
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).map
          (affineKoszulTopFunctionalSection R N p a) = 0 := by
  rw [affineKoszulGeometricClass_eq_restriction,schemeModule_pullback_map_zero_iff_unit]
end LinearStudy
