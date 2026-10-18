module
public import Linear.SchemeModuleHomTransportIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}
variable {A B A' B' N N' : X.Modules}
variable (s : A ≅ A') (t : B ≅ B') (e : N ≅ N')
variable (d : A ⟶ B) (d' : A' ⟶ B') (w : d ≫ t.hom = s.hom ≫ d')
/-- SAME differential-Hom cokernel transported through ACTUAL source/coefficient frames. Differential compatibility is derived from the original source square. -/
def schemeModuleHomArrowCokernelIso :
    cokernel (schemeModuleHomPrecompose (N := N) d) ≅
      cokernel (schemeModuleHomPrecompose (N := N') d') :=
  cokernel.mapIso _ _ (schemeModuleHomTransportIso t e) (schemeModuleHomTransportIso s e)
    (schemeModuleHomTransportIso_differential s t e d d' w)
/-- Preserve SAME actual cokernel projection in the constructed frames. -/
theorem schemeModuleHomArrowCokernelIso_projection :
    cokernel.π (schemeModuleHomPrecompose (N := N) d) ≫
        (schemeModuleHomArrowCokernelIso s t e d d' w).hom =
      (schemeModuleHomTransportIso s e).hom ≫ cokernel.π (schemeModuleHomPrecompose (N := N') d') :=
  cokernel.π_desc _ _ _
/-- SAME original functional class has the explicitly transported representative. -/
theorem schemeModuleHomArrowCokernelIso_class (a : A ⟶ N) :
    (schemeModuleHomUnitAddEquiv A N).symm a ≫
        cokernel.π (schemeModuleHomPrecompose (N := N) d) ≫
        (schemeModuleHomArrowCokernelIso s t e d d' w).hom =
      (schemeModuleHomUnitAddEquiv A' N').symm (s.inv ≫ a ≫ e.hom) ≫
        cokernel.π (schemeModuleHomPrecompose (N := N') d') := by
  rw [schemeModuleHomArrowCokernelIso_projection]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ cokernel.π (schemeModuleHomPrecompose (N := N') d'))
      (schemeModuleHomTransportIso_curry s e a)
end LinearStudy
