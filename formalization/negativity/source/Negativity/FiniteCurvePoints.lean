module

public import Negativity.CurveFiberDegree
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory IsDedekindDomain
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A codimension-one actual point in an affine chart determines an actual
height-one prime, with the point/prime inverse identity proved. -/
theorem curve_affine_point_heightOne (C : Scheme.{u}) [IsIntegral C]
    (U : C.Opens) (hU : IsAffineOpen U) (x : C) (hxU : x ∈ U)
    (hx : Order.coheight x = 1) :
    ∃ p : HeightOneSpectrum Γ(C, U), hU.fromSpec ⟨p.asIdeal, inferInstance⟩ = x := by
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have hp : p.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hU.fromSpec,
      hU.fromSpec_primeIdealOf]
    exact hx
  have hn : p.asIdeal ≠ ⊥ := by
    intro hz
    rw [hz, Ideal.height_bot] at hp
    norm_num at hp
  exact ⟨⟨p.asIdeal, inferInstance, hn⟩, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩

/-- Affine preimages of nonempty affine opens under a dominant finite map
are nonempty; no separate chart nonemptiness hypothesis is needed. -/
theorem finite_dominant_curve_preimage_nonempty {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] (U : Y.Opens) [Nonempty U] :
    Nonempty (f ⁻¹ᵁ U) := by
  have : Surjective f := surjective_of_isDominant_of_isClosed_range f
    f.isClosedMap.isClosed_range
  obtain ⟨y, hy⟩ := ‹Nonempty U›
  obtain ⟨x, hx⟩ := f.surjective y
  exact ⟨⟨x, by change f x ∈ U; rw [hx]; exact hy⟩⟩

/-- Final theorem: a finite dominant morphism of normal curves carries
actual codimension-one points to actual codimension-one points. This is
derived from contraction of integral height-one primes on actual affine
charts, rather than assumed as a divisor pushforward compatibility input. -/
theorem finite_normal_curve_maps_coheight_one {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdX : Order.krullDim X ≤ 1) (hdY : Order.krullDim Y ≤ 1)
    (x : X) (hx : Order.coheight x = 1) : Order.coheight (f x) = 1 := by
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f x) trivial
  have : Nonempty U := ⟨⟨f x, hyU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hyU⟩⟩
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have := normal_curve_affine_dedekind Y hnY hdY U hU
  have := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
  have := dominant_curve_chart_torsionFree f U
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  obtain ⟨q, hq⟩ := curve_affine_point_heightOne X (f ⁻¹ᵁ U) (hU.preimage f) x hyU hx
  let p := q.under Γ(Y, U)
  have : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let q' : p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U) := ⟨q.asIdeal, inferInstance, inferInstance⟩
  have he := curve_primeOver_maps_to_fiber f U hU ⟨p.asIdeal, inferInstance⟩ q'
  change f ((hU.preimage f).fromSpec ⟨q.asIdeal, inferInstance⟩) = _ at he
  rw [hq] at he
  rw [he]
  exact curve_affine_prime_coheight Y U hU p

end
end Negativity
