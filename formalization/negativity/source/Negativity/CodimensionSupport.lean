module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Negativity.CodimensionOne
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false

/-- In every dimension, a nonzero element of a Noetherian domain belongs
to only finitely many height-one primes. These primes are minimal over (r).
This does not assume a Dedekind coordinate ring or finite divisor support. -/
theorem finite_heightOne_primes_containing {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (r : R) (hr : r ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ r ∈ p.asIdeal}.Finite := by
  have hi : Function.Injective (fun p : PrimeSpectrum R ↦ p.asIdeal) :=
    fun p q h ↦ PrimeSpectrum.ext h
  apply ((Ideal.span {r}).finite_minimalPrimes_of_isNoetherianRing.preimage hi.injOn).subset
  intro p hp
  apply Ideal.mem_minimalPrimes_of_height_le
  · exact Ideal.span_le.mpr (by simpa using hp.2)
  · rw [hp.1]
    exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hr)

/-- On a nonempty affine chart of an integral locally Noetherian scheme,
the codimension-one points where a nonzero section is not a unit form a
finite set. This is the geometric support calculation used for Cartier data. -/
theorem finite_codimensionOne_nonunit_germs (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (r : Γ(X, U)) (hr : r ≠ 0) :
    {x : U | Order.coheight (x : X) = 1 ∧
      ¬ IsUnit (X.presheaf.germ U x x.2 r)}.Finite := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hi : Function.Injective hU.primeIdealOf := hU.isoSpec.hom.isOpenEmbedding.injective
  apply ((finite_heightOne_primes_containing r hr).preimage hi.injOn).subset
  intro x hx
  constructor
  · rw [idealHeight_eq_coheight]
    change Order.coheight (hU.isoSpec.hom x) = 1
    rw [coheight_eq_of_isOpenImmersion]
    exact (coheight_eq_of_isOpenImmersion (f := U.ι)).symm.trans hx.1
  · rw [hU.primeIdealOf_eq_map_closedPoint]
    change X.presheaf.germ U x x.2 r ∈ IsLocalRing.maximalIdeal _
    exact (IsLocalRing.mem_maximalIdeal _).mpr hx.2

end Negativity
