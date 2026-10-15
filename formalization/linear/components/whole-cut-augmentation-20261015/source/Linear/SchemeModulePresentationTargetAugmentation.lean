module
public import Linear.SchemeModulePresentationProjectionExists
public import Linear.ChainActualCokernelTargetAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- Transport the SAME proved original chart-adjoint formula to an
actual target identification. Construct a real chain augmentation and
prove its zero component,without assuming any desired target formula.
The target identification is explicit here;original applications build it. -/
theorem schemeModuleMappedPresentationDataTargetAugmentation_exists
    {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    [(Scheme.Modules.restrictFunctor j).Additive]
    [(Scheme.Modules.restrictFunctor j).PreservesHomology]
    (d : mappedChainPresentationData (Scheme.Modules.restrictFunctor j))
    (T : Y.Modules)
    (rho : (Scheme.Modules.pushforward j).obj d.2.2.2.1.pt ≅ T)
    (h : ∃ E : cokernel (d.1.d 1 0) ≅ (Scheme.Modules.pushforward j).obj d.2.2.2.1.pt,
      schemeModuleMappedPresentationDataGlobalProjection j d E) :
    ∃ E : cokernel (d.1.d 1 0) ≅ T,
      ∃ alpha : d.1 ⟶ (ChainComplex.single₀ Y.Modules).obj T,
        alpha = originalChainCokernelTargetAugmentation d.1 T E ∧
        alpha.f 0 =
          ((Scheme.Modules.restrictAdjunction j).homEquiv (d.1.X 0) d.2.2.2.1.pt)
            (d.2.2.1.hom.f 0 ≫ d.2.2.2.1.π) ≫ rho.hom := by
  obtain ⟨E,hE⟩ := h
  refine ⟨E ≪≫ rho,originalChainCokernelTargetAugmentation d.1 T (E ≪≫ rho),rfl,?_⟩
  rw [originalChainCokernelTargetAugmentation_f_zero]
  change cokernel.π (d.1.d 1 0) ≫ (E.hom ≫ rho.hom) = _
  rw [← Category.assoc]
  exact congrArg (fun g => g ≫ rho.hom) hE

end LinearStudy
