module
public import Linear.SchemeModuleHomOpenImmersionSourceNaturality
public import Linear.SchemeModuleRestrictionCokernel
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
/-- Restrict the ACTUAL original Hom/differential cokernel through the PROVED source square. No desired cokernel-comparison certificate is supplied. -/
def schemeModuleHomOpenImmersionCokernelIso
    {M' M : X.Modules} (N : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j] (d : M' ⟶ M) :
    (cokernel (schemeModuleHomPrecompose (N := N) d)).restrict j ≅
      cokernel (schemeModuleHomPrecompose (N := N.restrict j) ((Scheme.Modules.restrictFunctor j).map d)) :=
  schemeModuleOpenRestrictionCokernelIso j (schemeModuleHomPrecompose (N := N) d) ≪≫
    cokernel.mapIso
      ((Scheme.Modules.restrictFunctor j).map (schemeModuleHomPrecompose (N := N) d))
      (schemeModuleHomPrecompose (N := N.restrict j) ((Scheme.Modules.restrictFunctor j).map d))
      (schemeModuleHomOpenImmersionIso M N j) (schemeModuleHomOpenImmersionIso M' N j)
      (schemeModuleHomOpenImmersionIso_precompose N j d)
/-- Retain the SAME actual quotient projection,not merely equivalent objects. -/
theorem schemeModuleHomOpenImmersionCokernelIso_projection
    {M' M : X.Modules} (N : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j] (d : M' ⟶ M) :
    (Scheme.Modules.restrictFunctor j).map (cokernel.π (schemeModuleHomPrecompose (N := N) d)) ≫
        (schemeModuleHomOpenImmersionCokernelIso N j d).hom =
      (schemeModuleHomOpenImmersionIso M' N j).hom ≫
        cokernel.π (schemeModuleHomPrecompose (N := N.restrict j) ((Scheme.Modules.restrictFunctor j).map d)) := by
  dsimp only [schemeModuleHomOpenImmersionCokernelIso,Iso.trans_hom]
  rw [← Category.assoc,schemeModuleOpenRestrictionCokernelIso_projection]
  exact cokernel.π_desc _ _ _
end LinearStudy
