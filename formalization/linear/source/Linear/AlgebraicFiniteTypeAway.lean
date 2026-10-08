module
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
universe u

/-- Clear the finitely many generator denominators of an algebraic
finite-type algebra. Finiteness over a nonempty target open is a conclusion. -/
theorem algebraic_finiteType_exists_finite_away
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] [Algebra.IsAlgebraic R S] :
    ∃ r : R, r ≠ 0 ∧
      (Localization.awayMapₐ (Algebra.ofId R S) r).toRingHom.Finite := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := R) (A := S))
  obtain ⟨r, hr, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples R s
  let Rr := Localization.Away r
  let Sr := Localization.Away (algebraMap R S r)
  let φ := Localization.awayMapₐ (Algebra.ofId R S) r
  letI : Algebra Rr Sr := φ.toRingHom.toAlgebra
  letI : IsScalarTower R Rr Sr := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have hinv : algebraMap Rr Sr (IsLocalization.Away.invSelf r : Rr) *
      algebraMap R Sr r = 1 := by
    rw [IsScalarTower.algebraMap_apply R Rr Sr]
    calc
      algebraMap Rr Sr (IsLocalization.Away.invSelf r : Rr) *
          algebraMap Rr Sr (algebraMap R Rr r) =
        algebraMap Rr Sr ((IsLocalization.Away.invSelf r : Rr) * algebraMap R Rr r) :=
          (map_mul (algebraMap Rr Sr) _ _).symm
      _ = algebraMap Rr Sr 1 := congrArg (algebraMap Rr Sr)
        ((mul_comm _ _).trans (IsLocalization.Away.mul_invSelf r))
      _ = 1 := map_one _
  have hgen : ∀ z ∈ s, IsIntegral Rr (algebraMap S Sr z) := by
    intro z hz
    have hi : IsIntegral Rr (algebraMap S Sr (r • z)) :=
      ((hint z hz).algebraMap (B := Sr)).tower_top
    have he : (IsLocalization.Away.invSelf r : Rr) •
        algebraMap S Sr (r • z) = algebraMap S Sr z := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply R S Sr, ← mul_assoc, hinv, one_mul]
    exact he ▸ hi.smul (IsLocalization.Away.invSelf r : Rr)
  have hall : ∀ z : S, IsIntegral Rr (algebraMap S Sr z) := by
    intro z
    have hz : z ∈ Algebra.adjoin R (s : Set S) := by rw [hs]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem z hz => exact hgen z hz
    | algebraMap a =>
        rw [← IsScalarTower.algebraMap_apply R S Sr,
          IsScalarTower.algebraMap_apply R Rr Sr]
        exact isIntegral_algebraMap
    | add z w _ _ hz hw => simpa only [map_add] using hz.add hw
    | mul z w _ _ hz hw => simpa only [map_mul] using hz.mul hw
  letI : Algebra.IsIntegral Rr Sr := ⟨by
    intro z
    let u := IsLocalization.Away.sec (algebraMap R S r) z
    have he : z * algebraMap R Sr r ^ u.2 = algebraMap S Sr u.1 := by
      simpa only [u, map_pow, ← IsScalarTower.algebraMap_apply R S Sr] using
        IsLocalization.Away.sec_spec (algebraMap R S r) z
    have hi := (hall u.1).smul ((IsLocalization.Away.invSelf r : Rr) ^ u.2)
    have hc : ((IsLocalization.Away.invSelf r : Rr) ^ u.2) •
        algebraMap S Sr u.1 = z := by
      rw [Algebra.smul_def, he.symm, mul_left_comm, map_pow,
        ← mul_pow, hinv, one_pow, mul_one]
    exact hc ▸ hi⟩
  have hft : φ.toRingHom.FiniteType :=
    RingHom.finiteType_localizationPreserves.away (algebraMap R S) r Rr Sr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType Rr Sr := hft
  refine ⟨r, hr, ?_⟩
  change Module.Finite Rr Sr
  exact Algebra.finite_iff_isIntegral_and_finiteType.mpr ⟨inferInstance, inferInstance⟩

end LinearStudy
