module
public import Linear.SchemeModulePushforwardOpenSupport
public import Linear.SchemeModuleFlasqueKernelSectionLifting
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- Lift through any ACTUAL epi whose source is a subobject of Hom(f_*L,A), using the derived closed-discrete support of its kernel. -/
theorem schemeModule_unitHom_lift_of_closedDiscreteSubHom
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (L : D.Modules) (A M N : X.Modules)
    (j : M ⟶ schemeModuleHomModuleSheaf ((Scheme.Modules.pushforward f).obj L) A) [Mono j]
    (g : M ⟶ N) [Epi g] (s : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    ∃ t : SheafOfModules.unit X.ringCatSheaf ⟶ M, t ≫ g = s := by
  have hker := schemeModuleSubHom_pushforward_closedDiscreteFlasque f hf L A
    (kernel g) (kernel.ι g ≫ j)
  exact schemeModule_unitHom_lift_of_flasqueKernel g hker s
end LinearStudy
