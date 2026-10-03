module

public import Negativity.AffineValuationBase
public import Negativity.WeightedIdealExtension
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: actual kernel elements multiplied by a weight power
belong to every valuation ring containing the weighted base ideal.
The actual affine base map, dominant generic map, proper lift, ideal
contraction and all sums in the ideal extension are proved internally. -/
theorem actual_relative_kernel_weighted_valuation_mem
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (I : Y.IdealSheafData) (n : ℕ)
    (F : Type u) [Field F] (V : ValuationSubring F)
    (g : Γ(Y, ⊤) →+* V) (hg : Function.Injective g) (t : F)
    (hI : ∀ r ∈ I.ideal ⟨⊤, isAffineOpen_top Y⟩, (g r : F) * t ∈ V)
    (r : Γ(Y, ⊤)) (hr : r ∈ actualRelativeKernelIdeal f I n) :
    (g r : F) * t ^ n ∈ V := by
  let b := actualAffineRingBase Y g
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V F)) ≫ b) :=
    actual_affine_valuation_generic_dominant Y V F g hg
  have hcon := actual_relative_kernel_valuative_contraction f hf I n V F b
  have he : (Scheme.ΓSpecIso (.of V)).hom.hom.comp b.appTop.hom = g :=
    congrArg CommRingCat.Hom.hom (actual_affine_ring_base_sections Y g)
  have hc : (actualRelativeKernelIdeal f I n).map g ≤
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ n).map g := by
    have hm := Ideal.map_mono (f := (Scheme.ΓSpecIso (.of V)).hom.hom) hcon
    simpa only [Ideal.map_map, he] using hm
  exact weighted_ideal_extension_mem (I.ideal ⟨⊤, isAffineOpen_top Y⟩)
    V.toSubring g t hI n (g r) (hc (Ideal.mem_map_of_mem g hr))

end
end Negativity
