module

public import Negativity.FiniteCurveOrders
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.Opens) (hU : IsAffineOpen U)

local instance : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra

theorem curve_chart_point_mem (p : PrimeSpectrum Γ(Y, U)) : hU.fromSpec p ∈ U := by
  exact (hU.isoSpec.inv p).2

/-- Actual chart primes lying over p map to the actual geometric fiber. -/
theorem curve_primeOver_maps_to_fiber (p : PrimeSpectrum Γ(Y, U))
    (q : p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)) :
    f ((hU.preimage f).fromSpec ⟨q.1, inferInstance⟩) = hU.fromSpec p := by
  have hc : (⟨q.1, inferInstance⟩ : PrimeSpectrum Γ(X, f ⁻¹ᵁ U)).comap
      (f.app U).hom = p := by
    apply PrimeSpectrum.ext
    exact (Ideal.over_def q.1 p.asIdeal).symm
  have hs := congrArg (fun g : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y => g ⟨q.1, inferInstance⟩)
    (hU.SpecMap_appLE_fromSpec f (hU.preimage f) le_rfl)
  rw [← Scheme.Hom.app_eq_appLE] at hs
  simp only [Scheme.Hom.comp_apply] at hs
  change hU.fromSpec (Spec.map (f.app U) ⟨q.1, inferInstance⟩) =
    f ((hU.preimage f).fromSpec ⟨q.1, inferInstance⟩) at hs
  exact hs.symm.trans (congrArg hU.fromSpec hc)

/-- The actual point-to-prime map carries every geometric fiber point
to a prime lying over p, using the Scheme section-map square. -/
theorem curve_fiber_point_prime_liesOver (p : PrimeSpectrum Γ(Y, U))
    (x : X) (hx : f x = hU.fromSpec p) :
    let hxU : x ∈ f ⁻¹ᵁ U := show f x ∈ U from hx.symm ▸ curve_chart_point_mem U hU p
    ((hU.preimage f).primeIdealOf ⟨x, hxU⟩).asIdeal.LiesOver p.asIdeal := by
  have hxU : x ∈ f ⁻¹ᵁ U := show f x ∈ U from hx.symm ▸ curve_chart_point_mem U hU p
  have hc := IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U)
    (hU.preimage f) le_rfl hxU
  rw [← Scheme.Hom.app_eq_appLE] at hc
  change ((hU.preimage f).primeIdealOf ⟨x, hxU⟩).comap (f.app U).hom =
    hU.primeIdealOf ⟨f x, hxU⟩ at hc
  have hp : hU.primeIdealOf ⟨f x, hxU⟩ = p := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [hU.fromSpec_primeIdealOf]
    exact hx
  have he := congrArg PrimeSpectrum.asIdeal (hc.trans hp)
  exact ⟨he.symm⟩

/-- Final theorem: coordinate-ring primes over an actual affine-chart
point correspond bijectively to every actual point of its Scheme fiber.
The maps use actual affine point/prime identifications and the morphism's
section map; no fiber enumeration or point correspondence is assumed. -/
def curveFiberPrimeEquiv (p : PrimeSpectrum Γ(Y, U)) :
    p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U) ≃ {x : X // f x = hU.fromSpec p} where
  toFun q := ⟨(hU.preimage f).fromSpec ⟨q.1, inferInstance⟩,
    curve_primeOver_maps_to_fiber f U hU p q⟩
  invFun x :=
    let hxU : x.1 ∈ f ⁻¹ᵁ U := show f x.1 ∈ U from x.2.symm ▸ curve_chart_point_mem U hU p
    ⟨((hU.preimage f).primeIdealOf ⟨x, hxU⟩).asIdeal, inferInstance,
      curve_fiber_point_prime_liesOver f U hU p x x.2⟩
  left_inv q := by
    apply Subtype.ext
    change ((hU.preimage f).primeIdealOf
      ⟨(hU.preimage f).fromSpec ⟨q.1, inferInstance⟩, _⟩).asIdeal = q.1
    have he : (hU.preimage f).primeIdealOf
        ⟨(hU.preimage f).fromSpec ⟨q.1, inferInstance⟩,
          curve_chart_point_mem (f ⁻¹ᵁ U) (hU.preimage f) ⟨q.1, inferInstance⟩⟩ =
        (⟨q.1, inferInstance⟩ : PrimeSpectrum Γ(X, f ⁻¹ᵁ U)) := by
      apply (hU.preimage f).fromSpec.isOpenEmbedding.injective
      rw [(hU.preimage f).fromSpec_primeIdealOf]
    exact congrArg PrimeSpectrum.asIdeal he
  right_inv x := by
    apply Subtype.ext
    exact (hU.preimage f).fromSpec_primeIdealOf _

theorem curve_fiber_primes_actual_bijective (p : PrimeSpectrum Γ(Y, U)) :
    Function.Bijective (curveFiberPrimeEquiv f U hU p) :=
  (curveFiberPrimeEquiv f U hU p).bijective

end
end Negativity
