module
public import Linear.OriginalProjectiveWeightedChartScalarTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
theorem actualProjectiveChartOverlapPullback
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (r : Γ(Proj 𝒜, Proj.basicOpen 𝒜 a)) :
    let Ua := Proj.basicOpen 𝒜 a
    let Uab := Proj.basicOpen 𝒜 (a*b)
    let ea := Proj.basicOpenIsoSpec 𝒜 a ha (by decide)
    let eab := Proj.basicOpenIsoSpec 𝒜 (a*b) (SetLike.mul_mem_graded ha hb) (by decide)
    let φ := HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)
    eab.inv.appTop (Uab.topIso.inv
      ((Proj 𝒜).presheaf.map (homOfLE
        (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)).op r)) =
      (Spec.map (CommRingCat.ofHom φ)).appTop
        (ea.inv.appTop (Ua.topIso.inv r)) := by
  dsimp only
  obtain ⟨y,hy⟩ := (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway 𝒜 a ha (by decide)).hom).surjective r
  change Proj.awayToSection 𝒜 a y = r at hy
  subst r
  have hr : (Proj.awayToSection 𝒜 (a*b))
      (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) y) =
      (Proj 𝒜).presheaf.map (homOfLE
        (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)).op
        ((Proj.awayToSection 𝒜 a) y) := by
    exact congr($(Proj.awayMap_awayToSection 𝒜 hb (rfl : a*b=a*b)) y)
  rw [←hr]
  have ha' := congr($(originalProjectiveWeightedChartScalarTransport 𝒜
    1 (by decide) a ha) y)
  have hab' := congr($(originalProjectiveWeightedChartScalarTransport 𝒜
    2 (by decide) (a*b) (SetLike.mul_mem_graded ha hb))
      (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) y))
  have hn := congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))) y)
  exact hab'.trans (hn.trans (congrArg
    (fun z => (Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))).appTop z) ha'.symm))
end LinearStudy
