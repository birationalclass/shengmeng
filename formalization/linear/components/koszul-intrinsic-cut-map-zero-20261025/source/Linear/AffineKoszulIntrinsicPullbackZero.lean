module
public import Linear.SchemeModuleHomUnitFrameZero
public import Linear.AffineKoszulGeometricClassZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (p : ℕ)
/-- Vanishing of the SAME ordered Koszul coefficient section after the
ACTUAL pullback is precisely vanishing of the ORIGINAL coefficient
morphism. The ordered top exterior term is an ACTUAL source line;
no frame/freeness of N,conventional-frame equality or faithful pullback. -/
theorem affineKoszulTopFunctionalSection_pullback_zero_iff
    {Y : Scheme.{u}} (i : Y ⟶ Spec R)
    (a : tilde (ModuleCat.of R (⋀[R]^(p+1) (Fin (p+1) → R))) ⟶ tilde N) :
    (Scheme.Modules.pullback i).map (affineKoszulTopFunctionalSection R N p a)=0 ↔
      (Scheme.Modules.pullback i).map a=0 := by
  let s : SheafOfModules.unit (Spec R).ringCatSheaf ≅
      tilde (ModuleCat.of R (⋀[R]^(p+1) (Fin (p+1) → R))) :=
    (tildeSelf (R:=R)).symm ≪≫
      (tilde.functor R).mapIso (topKoszulEquiv (R:=R) (p+1)).symm.toModuleIso
  let phi : schemeModuleHomModuleSheaf
      (tilde (ModuleCat.of R (⋀[R]^(p+1) (Fin (p+1) → R)))) (tilde N) ≅ tilde N :=
    (affineKoszulTermHomCoefficientIso R N (p+1) (p+1)).symm ≪≫
      (tilde.functor R).mapIso (koszulTopHomCoefficientEquiv (N:=N) p).toModuleIso
  let F := Scheme.Modules.pullback i
  have hs : affineKoszulTopFunctionalSection R N p a=
      (schemeModuleHomUnitAddEquiv _ (tilde N)).symm a ≫ phi.hom := rfl
  rw [hs,F.map_comp]
  constructor
  · intro hz
    apply (schemeModuleLineFrame_curry_map_zero_iff F s a).mp
    apply (cancel_mono (F.map phi.hom)).mp
    simpa only [zero_comp] using hz
  · intro hz
    have hc := (schemeModuleLineFrame_curry_map_zero_iff F s a).mpr hz
    rw [hc,zero_comp]
/-- The SAME actual local class vanishes iff the ORIGINAL top functional
pulls back to zero on the ORIGINAL nonreduced cut. Neither an arbitrary
coefficient-section replacement nor a conventional sign/frame is used. -/
theorem affineKoszulGeometricClass_zero_iff_pullback_functional
    (H : Fin (p+1) → R)
    (a : tilde (ModuleCat.of R (⋀[R]^(p+1) (Fin (p+1) → R))) ⟶ tilde N) :
    (schemeModuleHomUnitAddEquiv _ (tilde N)).symm a ≫
        (affineKoszulHomGeometricRestrictionPresentation R N p H).g=0 ↔
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).map a=0 := by
  exact (affineKoszulGeometricClass_zero_iff_pullback R N p H a).trans
    (affineKoszulTopFunctionalSection_pullback_zero_iff R N p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H))))) a)
end LinearStudy
