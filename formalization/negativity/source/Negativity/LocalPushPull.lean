module

public import Negativity.Projection
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory IsDiscreteValuationRing

/-- A local-ring isomorphism preserves the normalized valuation of a DVR.
This is the local coefficient calculation at a nonexceptional prime divisor. -/
theorem dvr_order_ringEquiv {R S : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (e : R ≃+* S) (a : R) :
    addVal S (e a) = addVal R a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨p, hp⟩ := exists_prime R
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible ha hp.irreducible
  have hep : Irreducible (e p) := hp.irreducible.map e
  rw [addVal_def a u hp.irreducible n hu]
  apply addVal_def (e a) (Units.map e.toMonoidHom u) hep n
  simpa using congrArg e hu

/-- Signed order of a nonzero rational local equation represented as a/b.
Zero numerator/denominator are excluded in the invariance theorem below. -/
noncomputable def LocalFractionOrder (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (a b : R) : ℤ :=
  ((addVal R a).toNat : ℤ) - ((addVal R b).toNat : ℤ)

/-- The signed local order is independent of the chosen nonzero fraction
representation. Thus this coefficient calculation is not an arbitrary pairing. -/
theorem dvr_fraction_order_well_defined {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (a b c d : R)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : LocalFractionOrder R a b = LocalFractionOrder R c d := by
  have va : addVal R a ≠ ⊤ := by simpa [addVal_eq_top_iff] using ha
  have vb : addVal R b ≠ ⊤ := by simpa [addVal_eq_top_iff] using hb
  have vc : addVal R c ≠ ⊤ := by simpa [addVal_eq_top_iff] using hc
  have vd : addVal R d ≠ ⊤ := by simpa [addVal_eq_top_iff] using hd
  have hv := congrArg (fun z => (addVal R z).toNat) h
  rw [addVal_mul, addVal_mul, ENat.toNat_add va vd, ENat.toNat_add vc vb] at hv
  unfold LocalFractionOrder
  omega

/-- A local-ring isomorphism preserves the signed order of rational local equations. -/
theorem dvr_fraction_order_ringEquiv {R S : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (e : R ≃+* S) (a b : R) :
    LocalFractionOrder S (e a) (e b) = LocalFractionOrder R a b := by
  simp [LocalFractionOrder, dvr_order_ringEquiv]

/-- A coefficientwise criterion for push-pull, using the actual Scheme-cycle map.
The chosen strict transforms, coefficient agreement, unit degree and exceptional
weight drop remain local geometric inputs; no push-pull equality is assumed. -/
theorem scheme_pushpull_of_local_coefficients {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    (D : AlgebraicCycle Y ℝ) (lifted : AlgebraicCycle X ℝ) (strict : Y → X)
    (hcoeff : ∀ y, lifted (strict y) = D y)
    (hsection : ∀ y, D y ≠ 0 → f.base (strict y) = y)
    (hdegree : ∀ y, D y ≠ 0 → AlgebraicCycle.mapCoeff f wx wy (strict y) = 1)
    (hexceptional : ∀ x, x ≠ strict (f.base x) →
      lifted x = 0 ∨ wx x ≠ wy (f.base x)) :
    AlgebraicCycle.map f wx wy lifted = D := by
  ext y
  change (∑ᶠ x ∈ f.base ⁻¹' {y}, lifted x *
    (AlgebraicCycle.mapCoeff f wx wy x : ℝ)) = D y
  have hz : ∀ x, x ≠ strict y →
      (∑ᶠ (_ : x ∈ f.base ⁻¹' {y}), lifted x *
        (AlgebraicCycle.mapCoeff f wx wy x : ℝ)) = 0 := by
    intro x hx
    by_cases hxy : f.base x = y
    · have hx' : x ≠ strict (f.base x) := by simpa [hxy] using hx
      rcases hexceptional x hx' with hzero | hdrop
      · simp [hzero]
      · simp [scheme_mapCoeff_zero_of_drop f wx wy x hdrop]
    · simp [Set.mem_preimage, Set.mem_singleton_iff, hxy]
  rw [finsum_eq_single _ (strict y) hz]
  by_cases hD : D y = 0
  · simp [hcoeff, hD]
  · simp [hsection y hD, hcoeff, hdegree y hD]

/-- The same coefficient invariance at actual Scheme stalks when the stalk map
is an isomorphism. DVR hypotheses on these stalks are explicit. -/
theorem scheme_stalk_fraction_order_of_iso {X Y : Scheme} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)]
    [IsDomain (Y.presheaf.stalk (f x))] [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (Y.presheaf.stalk (f x))]
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (a b : Y.presheaf.stalk (f x)) :
    LocalFractionOrder (X.presheaf.stalk x) ((f.stalkMap x).hom a) ((f.stalkMap x).hom b) =
      LocalFractionOrder (Y.presheaf.stalk (f x)) a b := by
  exact dvr_fraction_order_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv a b

/-- An actual residue-field isomorphism forces the actual cycle multiplicity degree to one. -/
theorem scheme_residueDegree_of_iso {X Y : Scheme} (f : X ⟶ Y) (x : X)
    [IsIso (f.residueFieldMap x)] : f.residueDegree x = 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  change Module.finrank (Y.residueField (f x)) (X.residueField x) = 1
  exact Module.finrank_of_bijective_algebraMap
    (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.bijective

/-- A Scheme stalk isomorphism induces a residue-field isomorphism and degree one. -/
theorem scheme_residueDegree_of_stalk_iso {X Y : Scheme} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] : f.residueDegree x = 1 := by
  have : IsIso (f.residueFieldMap x) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  exact scheme_residueDegree_of_iso f x
/-- Replace the degree-one condition by an actual residue-field isomorphism.
Local strict-transform coefficients and exceptional dimension drop still need
construction from proper birational geometry and actual Cartier pullback. -/
theorem scheme_pushpull_of_local_isomorphisms {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    (D : AlgebraicCycle Y ℝ) (lifted : AlgebraicCycle X ℝ) (strict : Y → X)
    (hcoeff : ∀ y, lifted (strict y) = D y)
    (hsection : ∀ y, D y ≠ 0 → f.base (strict y) = y)
    (hweight : ∀ y, D y ≠ 0 → wx (strict y) = wy (f.base (strict y)))
    (hstalk : ∀ y, D y ≠ 0 → IsIso (f.stalkMap (strict y)))
    (hexceptional : ∀ x, x ≠ strict (f.base x) →
      lifted x = 0 ∨ wx x ≠ wy (f.base x)) :
    AlgebraicCycle.map f wx wy lifted = D := by
  apply scheme_pushpull_of_local_coefficients f wx wy D lifted strict hcoeff hsection
  · intro y hy
    have := hstalk y hy
    rw [scheme_mapCoeff_of_same_weight f wx wy (strict y) (hweight y hy),
      scheme_residueDegree_of_stalk_iso]
  · exact hexceptional
end Negativity
