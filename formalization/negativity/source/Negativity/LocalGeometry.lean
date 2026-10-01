module

public import Negativity.LocalPushPull
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Tactic

@[expose] public section
namespace Negativity
universe u
open AlgebraicGeometry CategoryTheory IsLocalRing Ring

/-- The standard normal one-dimensional local-ring lemma, deduced from
mathlib's verified DVR characterization; DVR is not an input. -/
theorem normal_one_dimensional_local_isDVR (R : Type*) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hfield : ¬ IsField R := by
    intro h
    have hzero := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at hzero
    exact one_ne_zero hzero
  have : KrullDimLE 1 R := krullDimLE_iff.mpr hdim.le
  have hprime : ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = maximalIdeal R := by
    intro P hP hp
    exact eq_maximalIdeal (hp.isMaximal_of_ne_bot hP)
  have hnormal : IsIntegrallyClosed R ∧
      ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = maximalIdeal R :=
    ⟨inferInstance, hprime⟩
  have : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 1).mp hnormal
  exact { not_a_field' := isField_iff_maximalIdeal_eq.not.mp hfield }

/-- For an actual locally Noetherian integral Scheme, an integrally closed
one-dimensional stalk is a DVR. The dimension hypothesis is explicit: identifying
it with a geometric codimension-one point is a further geometry step. -/
theorem scheme_normal_one_dimensional_stalk_isDVR (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) :=
  normal_one_dimensional_local_isDVR _ hdim

/-- A proper actual Scheme morphism has a lift for any DVR/fraction-field square.
The square's top map must still be constructed from the birational generic data
in the codimension-one application. No lift-existence input is assumed. -/
theorem proper_dvr_lift {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (top : Spec (.of K) ⟶ X) (bottom : Spec (.of R) ⟶ Y)
    (w : top ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ bottom) :
    ∃ lift : Spec (.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ lift = top ∧
      lift ≫ f = bottom := by
  have hp : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) f := by
    rw [← IsProper.eq_valuativeCriterion]
    exact inferInstance
  let square : ValuativeCommSq f := {R := R, K := K, i₁ := top, i₂ := bottom, commSq := ⟨w⟩}
  obtain ⟨lift⟩ := ((ValuativeCriterion.existence hp.1.1.1) square).exists_lift
  exact ⟨lift.l, lift.fac_left, lift.fac_right⟩

/-- Properness also gives uniqueness, through the already verified separated
valuative criterion. The square is any actual valuative square, including DVRs. -/
theorem proper_valuative_lift_unique {X Y : Scheme} (f : X ⟶ Y) [IsProper f]
    (square : ValuativeCommSq f) : Subsingleton square.commSq.LiftStruct :=
  IsSeparated.valuativeCriterion f square

/-- Reuse mathlib's proved Zariski-main corollary on actual Scheme morphisms.
This is a library integration, not a new proof of Zariski's main theorem. -/
theorem proper_quasiFinite_isFinite {X Y : Scheme} (f : X ⟶ Y)
    [IsProper f] [LocallyQuasiFinite f] : IsFinite f :=
  IsFinite.of_isProper_of_locallyQuasiFinite f

/-- A finite fiber of a proper morphism has a neighborhood on which the
morphism is finite. Birationality/normality must still turn finite into iso. -/
theorem proper_finite_fiber_neighborhood {X Y : Scheme} (f : X ⟶ Y)
    [IsProper f] (y : Y) (hfinite : (f ⁻¹' {y}).Finite) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) :=
  exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y hfinite

end Negativity
