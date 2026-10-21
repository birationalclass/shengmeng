module
public import Linear.AcyclicChainHomExtension
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u v
/-- Positive exactness of ACTUAL Hom cochains into EVERY coefficient forces actual
source chain exactness.The opcycle identity extends,so the native opcycle map is monic. -/
theorem chain_exactAt_of_all_actualHom_exactAt {A : Type u} [Category.{v} A] [Abelian A]
    (K : ChainComplex A ℕ) (p : ℕ)
    (h : ∀ F : A, (chainActualHomCochain K F).ExactAt (p+1)) : K.ExactAt (p+1) := by
  obtain ⟨b,hb⟩ := chainActualHomExact_opcycle_extension K (K.opcycles (p+1)) p
    (h _) (𝟙 _)
  haveI : Mono (K.fromOpcycles (p+1) p) := mono_of_mono_fac hb
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact KernelFork.IsLimit.isZero_of_mono (K.homologyIsKernel (p+1) p (by simp))
end LinearStudy
