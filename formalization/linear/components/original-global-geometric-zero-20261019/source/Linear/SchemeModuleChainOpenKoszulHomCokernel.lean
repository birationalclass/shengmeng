module
public import Linear.SchemeModuleHomOpenImmersionCokernelClass
public import Linear.AffineKoszulFramedHomCokernel
public import Linear.TildeComplexExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
variable (R : CommRingCat.{u}) {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
variable (p : ℕ) (H : Fin (p+1) → R) (C : ChainComplex X.Modules ℕ)
variable (gamma : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅
  tildeFunctionKoszulComplex R H)
/-- Degreewise frame of the SAME actual restricted original chain iso. -/
def schemeModuleChainOpenKoszulTermIso (q : ℕ) :
    (C.X q).restrict j ≅ tilde (ModuleCat.of R (⋀[R]^q (Fin (p+1) → R))) :=
  (HomologicalComplex.eval (Spec R).Modules (ComplexShape.down ℕ) q).mapIso gamma
/-- The original source differential square is DERIVED from the actual chain map. -/
theorem schemeModuleChainOpenKoszulTermIso_differential :
    (Scheme.Modules.restrictFunctor j).map (C.d (p+1) p) ≫
        (schemeModuleChainOpenKoszulTermIso R j p H C gamma p).hom =
      (schemeModuleChainOpenKoszulTermIso R j p H C gamma (p+1)).hom ≫
        (tilde.functor R).map (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) p)) :=
  by
    have h := (gamma.hom.comm (p+1) p).symm
    change (Scheme.Modules.restrictFunctor j).map (C.d (p+1) p) ≫ gamma.hom.f p =
      gamma.hom.f (p+1) ≫ (tilde.functor R).map
        ((koszulComplex (Fintype.linearCombination R H)).d (p+1) p) at h
    rw [koszulComplex.d_eq_d] at h
    exact h
variable (N : X.Modules) (T : ModuleCat.{u} R) (beta : N.restrict j ≅ tilde T)
/-- ACTUAL restricted original highest-Hom cokernel computed on the SAME Koszul chart. The desired source differential/Hom/cokernel squares are all proved,not extra assumptions. -/
def schemeModuleChainOpenKoszulHomCokernelIso :
    (cokernel (schemeModuleHomPrecompose (N := N) (C.d (p+1) p))).restrict j ≅
      (affineKoszulHomGeometricRestrictionPresentation R T p H).X₃ :=
  schemeModuleHomOpenImmersionCokernelIso N j (C.d (p+1) p) ≪≫
    affineKoszulFramedHomCokernelIso R T p H
      (schemeModuleChainOpenKoszulTermIso R j p H C gamma (p+1))
      (schemeModuleChainOpenKoszulTermIso R j p H C gamma p) beta
      ((Scheme.Modules.restrictFunctor j).map (C.d (p+1) p))
      (schemeModuleChainOpenKoszulTermIso_differential R j p H C gamma)
/-- SAME original quotient functional restricts to the explicitly framed original functional on the SAME geometric cut. -/
theorem schemeModuleChainOpenKoszulHomCokernelIso_class (a : C.X (p+1) ⟶ N) :
    (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map
          ((schemeModuleHomUnitAddEquiv (C.X (p+1)) N).symm a ≫
            cokernel.π (schemeModuleHomPrecompose (N := N) (C.d (p+1) p))) ≫
        (schemeModuleChainOpenKoszulHomCokernelIso R j p H C gamma N T beta).hom =
      (schemeModuleHomUnitAddEquiv _ (tilde T)).symm
          ((schemeModuleChainOpenKoszulTermIso R j p H C gamma (p+1)).inv ≫
            (Scheme.Modules.restrictFunctor j).map a ≫ beta.hom) ≫
        (affineKoszulHomGeometricRestrictionPresentation R T p H).g := by
  dsimp only [schemeModuleChainOpenKoszulHomCokernelIso,Iso.trans_hom]
  rw [← Category.assoc]
  have hc := schemeModuleHomOpenImmersionCokernelIso_class j (C.d (p+1) p) a
  have ht := affineKoszulFramedHomCokernelIso_class R T p H
    (schemeModuleChainOpenKoszulTermIso R j p H C gamma (p+1))
    (schemeModuleChainOpenKoszulTermIso R j p H C gamma p) beta
    ((Scheme.Modules.restrictFunctor j).map (C.d (p+1) p))
    (schemeModuleChainOpenKoszulTermIso_differential R j p H C gamma)
    ((Scheme.Modules.restrictFunctor j).map a)
  calc
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z => z ≫ _) hc
    _ = _ := by simpa only [Category.assoc] using ht
end LinearStudy
