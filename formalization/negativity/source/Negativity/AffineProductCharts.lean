module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the simultaneous inverse image of actual affine opens
in a genuine scheme fiber product over an actual affine base is affine.
The actual open is identified with the image of the actual affine fiber
product of the two source opens; no affineness of the projections or
affineness of the resulting intersection is an input. -/
theorem actual_affine_product_chart
    {X Y S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let p : pullback (U.ι ≫ f) (V.ι ≫ g) ⟶ pullback f g :=
    pullback.map _ _ _ _ U.ι V.ι (𝟙 S) (by simp) (by simp)
  have : IsOpenImmersion p := by dsimp [p]; infer_instance
  have heq : p.opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    apply Opens.ext
    simp [p, Scheme.Pullback.range_map]
  rw [← heq]
  exact isAffineOpen_opensRange p

end
end Negativity
