module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
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

/-- On the SAME original Proj positive-degree chart (including actual degree-two overlaps), transport of its
actual chart scalar to Spec is the original global Spec section map.
This closes the scalar square used for source-dual tilde restriction. -/
theorem originalProjectiveWeightedChartScalarTransport (d : ℕ) (hd : 0 < d) (a : S) (ha : a ∈ 𝓑 d) :
    let U := Proj.basicOpen 𝓑 a
    let e := Proj.basicOpenIsoSpec 𝓑 a ha hd
    Proj.awayToSection 𝓑 a ≫ U.topIso.inv ≫ e.inv.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).inv := by
  let U := Proj.basicOpen 𝓑 a
  let e := Proj.basicOpenIsoSpec 𝓑 a ha hd
  dsimp only
  have he : e.hom.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).hom ≫
        Proj.awayToSection 𝓑 a ≫ U.topIso.inv := by
    exact Proj.basicOpenToSpec_app_top 𝓑 a
  have hi : e.hom.appTop ≫ e.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
  apply (cancel_epi (Scheme.ΓSpecIso
    (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).hom).mp
  rw [he] at hi
  simpa only [Category.assoc, Iso.hom_inv_id] using hi

end LinearStudy
