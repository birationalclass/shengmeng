module
public import Linear.SchemeModuleHomArrowCokernel
public import Linear.AffineKoszulHomGeometricCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
variable {A B M : (Spec R).Modules}
variable (s : A ≅ tilde (ModuleCat.of R (⋀[R]^(p+1) (Fin (p+1) → R))))
variable (t : B ≅ tilde (ModuleCat.of R (⋀[R]^p (Fin (p+1) → R)))) (e : M ≅ tilde N)
variable (d : A ⟶ B)
variable (w : d ≫ t.hom = s.hom ≫ (tilde.functor R).map
  (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) p)))
/-- Original framed top Hom-differential cokernel is SAME geometric cut coefficient. Actual source-square and actual frames suffice;no Hom/cokernel comparison certificate is assumed. -/
def affineKoszulFramedHomCokernelIso :
    cokernel (schemeModuleHomPrecompose (N := M) d) ≅
      (affineKoszulHomGeometricRestrictionPresentation R N p H).X₃ :=
  schemeModuleHomArrowCokernelIso s t e d
    ((tilde.functor R).map (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) p))) w ≪≫
      affineKoszulHomGeometricCokernelIso R N p H
/-- SAME original quotient projection is the actual framed geometric restriction map. -/
theorem affineKoszulFramedHomCokernelIso_projection :
    cokernel.π (schemeModuleHomPrecompose (N := M) d) ≫
        (affineKoszulFramedHomCokernelIso R N p H s t e d w).hom =
      (schemeModuleHomTransportIso s e).hom ≫
        (affineKoszulHomGeometricRestrictionPresentation R N p H).g := by
  dsimp only [affineKoszulFramedHomCokernelIso,Iso.trans_hom]
  rw [← Category.assoc,schemeModuleHomArrowCokernelIso_projection]
  simpa only [Category.assoc] using
    congrArg (fun z => (schemeModuleHomTransportIso s e).hom ≫ z)
      (affineKoszulHomGeometricCokernelIso_projection R N p H)
/-- SAME original functional maps to its SAME framed geometric cut restriction. The representative is explicitly s.inv followed by original a and coefficient frame e. -/
theorem affineKoszulFramedHomCokernelIso_class (a : A ⟶ M) :
    (schemeModuleHomUnitAddEquiv A M).symm a ≫
        cokernel.π (schemeModuleHomPrecompose (N := M) d) ≫
        (affineKoszulFramedHomCokernelIso R N p H s t e d w).hom =
      (schemeModuleHomUnitAddEquiv _ (tilde N)).symm (s.inv ≫ a ≫ e.hom) ≫
        (affineKoszulHomGeometricRestrictionPresentation R N p H).g := by
  rw [affineKoszulFramedHomCokernelIso_projection]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ (affineKoszulHomGeometricRestrictionPresentation R N p H).g)
      (schemeModuleHomTransportIso_curry s e a)
end LinearStudy
