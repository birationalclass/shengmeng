module

public import Negativity.NormalExtension
public import Negativity.CartierSupport
public import Negativity.RealCartierDecomposition
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace IsDiscreteValuationRing
set_option backward.isDefEq.respectTransparency false

/-- Nonnegative signed order in a DVR is equivalent to the rational
equation being an actual element of the valuation ring. -/
theorem dvr_rationalOrder_nonneg_iff_regular (R K : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (a : Kˣ) :
    0 ≤ DvrRationalOrder R K a ↔ ∃ r : R, algebraMap R K r = (a : K) := by
  constructor
  · intro hn
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj (nonZeroDivisors R) (a : K)
    have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
    have hsk : algebraMap R K (s : R) ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hs
    have hr : r ≠ 0 := by
      intro hz
      exact mul_ne_zero a.ne_zero hsk (by simpa [hz] using he)
    rw [dvr_rationalOrder_represents R K a r s hr hs he] at hn
    have vr : addVal R r ≠ ⊤ := fun h => hr (addVal_eq_top_iff.mp h)
    have vs : addVal R (s : R) ≠ ⊤ := fun h => hs (addVal_eq_top_iff.mp h)
    have hle : (addVal R (s : R)).toNat ≤ (addVal R r).toNat := by
      unfold LocalFractionOrder at hn
      omega
    have hle' : addVal R (s : R) ≤ addVal R r := by
      rw [← ENat.natCast_toNat vs, ← ENat.natCast_toNat vr]
      exact_mod_cast hle
    obtain ⟨t, ht⟩ := addVal_le_iff_dvd.mp hle'
    refine ⟨t, ?_⟩
    apply mul_right_cancel₀ hsk
    rw [he, ht, map_mul, mul_comm]
  · rintro ⟨r, hr⟩
    have hne : r ≠ 0 := by
      intro hz
      exact a.ne_zero (by simpa [hz] using hr.symm)
    rw [dvr_rationalOrder_represents R K a r 1 hne one_ne_zero (by simpa using hr.symm)]
    simp [LocalFractionOrder]

/-- A nonzero rational equation on a normal affine open is regular when
all its actual codimension-one orders are nonnegative. The extension
step is the proved normal-domain theorem, applied to actual stalks. -/
theorem normal_affine_rational_regular (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (a : X.functionFieldˣ)
    (horder : ∀ (x : X) (hx : x ∈ U) (hc : Order.coheight x = 1),
      0 ≤ schemeRationalOrder X hn x hc a) :
    ∃ r : Γ(X, U), algebraMap Γ(X, U) X.functionField r = (a : X.functionField) := by
  classical
  let R := Γ(X, U)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed R := normal_affine_sections X hn U hU
  have : IsFractionRing R X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  apply normal_fraction_regular_of_height_one_denominators R X.functionField (a : X.functionField)
  intro p _ hp
  let S : Type _ := X.presheaf.stalk (hU.fromSpec ⟨p, inferInstance⟩)
  let : Algebra R S := X.presheaf.algebra_section_stalk
    ⟨hU.fromSpec ⟨p, inferInstance⟩, (hU.isoSpec.inv _).2⟩
  have : IsLocalization.AtPrime S p :=
    hU.isLocalization_stalk' ⟨p, inferInstance⟩ (hU.isoSpec.inv _).2
  have : IsScalarTower R S X.functionField := functionField_isScalarTower X U
    ⟨hU.fromSpec ⟨p, inferInstance⟩, (hU.isoSpec.inv _).2⟩
  have hc : Order.coheight (hU.fromSpec ⟨p, inferInstance⟩) = 1 := by
    rw [coheight_eq_of_isOpenImmersion (f := hU.fromSpec), ← idealHeight_eq_coheight]
    exact hp
  have := hn (hU.fromSpec ⟨p, inferInstance⟩)
  have := normal_codimensionOne_stalk_isDVR X (hU.fromSpec ⟨p, inferInstance⟩) hc
  obtain ⟨y, hy⟩ := (dvr_rationalOrder_nonneg_iff_regular S X.functionField a).mp
    (horder _ (hU.isoSpec.inv _).2 hc)
  obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.primeCompl y
  refine ⟨r, s, s.2, ?_⟩
  have he' := congrArg (algebraMap S X.functionField) he
  simpa only [map_mul, ← IsScalarTower.algebraMap_apply R S X.functionField, hy] using he'

/-- On an actual normal locally Noetherian scheme, a Cartier divisor is
effective exactly when all of its actual Weil coefficients are nonnegative.
In particular, regular local equations are now outputs, not assumptions. -/
theorem cartierAtlas_effective_iff_weil_nonneg (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) :
    A.Effective ↔ ∀ x : X, 0 ≤ A.weilCycle hn x := by
  constructor
  · exact effective_cartierAtlas_weil_nonneg X hn A
  · intro h
    intro i x hx
    have : Nonempty (A.chart i) := A.nonempty i
    obtain ⟨r, hr⟩ := normal_affine_rational_regular X hn (A.chart i) (A.affine i)
      (A.equation i) (by
        intro y hy hc
        have hh := h y
        change 0 ≤ A.coefficient hn y at hh
        rwa [cartierAtlas_coefficient_eq X hn A i y hc hy] at hh)
    refine ⟨X.presheaf.germ (A.chart i) x hx r, ?_⟩
    exact (Scheme.algebraMap_germ_eq_germToFunctionField X hx r).trans hr

/-- An effective actual real Weil combination of Cartier presentations
decomposes into nonnegative real multiples of actual effective Cartier
presentations. Effectivity of the resulting local equations is proved.
The equality is an equality of constructed Weil cycles. -/
theorem exists_realCartier_effective_weil_decomposition (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (c : τ → ℝ)
    (he : ∀ x : X, 0 ≤ ∑ t, c t * ((A t).coefficient hn x : ℝ)) :
    ∃ (J : Type) (_ : Fintype J) (w : J → ℝ) (B : J → CartierAtlas X X),
      (∀ j, 0 ≤ w j) ∧ (∀ j, (B j).Effective) ∧
      (∀ j x, (∑ t, c t * ((A t).coefficient hn x : ℝ)) = 0 →
        (B j).coefficient hn x = 0) ∧
      (∑ j, (B j).weightedWeilCycle hn (w j)) =
        ∑ t, (A t).weightedWeilCycle hn (c t) := by
  obtain ⟨J, hJ, w, B, hw, heff, hz, heq⟩ :=
    exists_realCartier_nonnegative_weil_decomposition X hn A c he
  refine ⟨J, hJ, w, B, hw, ?_, hz, heq⟩
  intro j
  apply (cartierAtlas_effective_iff_weil_nonneg X hn (B j)).mpr
  exact heff j

end Negativity
