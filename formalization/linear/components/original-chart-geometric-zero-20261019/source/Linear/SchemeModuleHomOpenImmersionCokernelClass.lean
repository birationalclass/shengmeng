module
public import Linear.SchemeModuleHomOpenImmersionCokernel
public import Linear.SchemeModuleHomOpenImmersionCurry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y : Scheme.{u}}
/-- SAME original functional class restricts to SAME actual restricted functional modulo SAME restricted differential. This proves a morphism identity,not only an isomorphism of objects. -/
theorem schemeModuleHomOpenImmersionCokernelIso_class
    {M' M N : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    (d : M' ⟶ M) (a : M' ⟶ N) :
    (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map
          ((schemeModuleHomUnitAddEquiv M' N).symm a ≫
            cokernel.π (schemeModuleHomPrecompose (N := N) d)) ≫
        (schemeModuleHomOpenImmersionCokernelIso N j d).hom =
      (schemeModuleHomUnitAddEquiv (M'.restrict j) (N.restrict j)).symm
          ((Scheme.Modules.restrictFunctor j).map a) ≫
        cokernel.π (schemeModuleHomPrecompose (N := N.restrict j)
          ((Scheme.Modules.restrictFunctor j).map d)) := by
  rw [Functor.map_comp,Category.assoc,schemeModuleHomOpenImmersionCokernelIso_projection]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ cokernel.π (schemeModuleHomPrecompose (N := N.restrict j)
      ((Scheme.Modules.restrictFunctor j).map d))) (schemeModuleHomOpenImmersionIso_curry j a)
end LinearStudy
