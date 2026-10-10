module
public import Linear.AffineQuasicoherentSectionsSurjective
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- On an actual affine open immersion, the original sheaf epimorphism
is surjective on sections of its image. Quasicoherence is preserved by
the actual restriction functor; its left adjoint structure preserves epi. -/
theorem quasicoherent_sections_surjective_on_affineOpen
    {X : Scheme.{u}} (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] :
    Function.Surjective (f.app (j ''ᵁ ⊤)) := by
  let F := Scheme.Modules.restrictFunctor j
  haveI : Epi (F.map f) := inferInstance
  have h := affineQuasicoherent_globalSections_surjective R (F.map f)
  change Function.Surjective (f.app (j ''ᵁ ⊤)) at h
  exact h

/-- Actual sections on the original native positive-degree Proj chart
carry a quasi-coherent sheaf epimorphism to a surjection. No surjectivity
certificate or chart model is assumed. -/
theorem quasicoherent_sections_surjective_on_nativeProjChart
    {K S : Type u} [Field K] [CommRing S] [Algebra K S]
    (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
    (d : ℕ) (hd : 0 < d) (a : S) (ha : a ∈ 𝓑 d)
    {M N : (Proj 𝓑).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] :
    Function.Surjective (f.app (Proj.basicOpen 𝓑 a)) := by
  have h := quasicoherent_sections_surjective_on_affineOpen
    (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)) (Proj.awayι 𝓑 a ha hd) f
  rw [Scheme.Hom.image_top_eq_opensRange, Proj.opensRange_awayι] at h
  exact h

end LinearStudy
