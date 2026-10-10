module
public import Linear.OriginalProjectiveChartScalarTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

theorem originalProjectiveChartScalar_appLE (a : S) (ha : a ∈ 𝓑 1) :
    Proj.awayToSection 𝓑 a ≫
      (Proj.awayι 𝓑 a ha (by decide)).appLE (Proj.basicOpen 𝓑 a) ⊤
        (by simp [Proj.awayι, Scheme.Hom.comp_preimage]) =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).inv := by
  let U := Proj.basicOpen 𝓑 a
  let e := Proj.basicOpenIsoSpec 𝓑 a ha (by decide)
  have hi : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv, eqToHom_op]
    rfl
  have hc : (Proj.awayι 𝓑 a ha (by decide)).appLE U ⊤
      (by simp [Proj.awayι, Scheme.Hom.comp_preimage, U]) =
      U.ι.appLE U ⊤ (by simp) ≫ e.inv.appTop := by
    exact (Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤ (by simp) (by simp)).symm
  change Proj.awayToSection 𝓑 a ≫ _ = _
  rw [hc,hi]
  exact originalProjectiveChartScalarTransport 𝓑 a ha

end LinearStudy
