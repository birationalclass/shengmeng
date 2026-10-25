module
public import Linear.RegularSequenceMaximalLocalization
public import Linear.FiniteReducedLocalCut
public import Linear.OriginRegular
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open RingTheory.Sequence
/-- Finiteness alone derives Artinianity of the ACTUAL closed fiber of a
finite algebra over a local ring. No reducedness or flatness is assumed. -/
theorem finite_algebra_closed_fiber_artinian
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] :
    IsArtinianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  let m := IsLocalRing.maximalIdeal R
  let I := m.map (algebraMap R S)
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  letI : Algebra (R ⧸ m) (S ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap (R:=R) (A:=S) (p:=m) (P:=I) Ideal.le_comap_map
  letI : IsScalarTower R (R ⧸ m) (S ⧸ I) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Module.Finite R (S ⧸ I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective
  letI : Module.Finite (R ⧸ m) (S ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ m) (S ⧸ I)
  exact IsArtinianRing.of_finite (R ⧸ m) (S ⧸ I)
/-- Every actual source maximal ideal of a finite local-base algebra lies
above the base maximal ideal. The fiber-support inclusion is derived. -/
theorem finite_algebra_maximal_contains_base_maximal
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] (P : Ideal S) [P.IsMaximal] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ P := by
  have hc := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R:=R) (S:=S) P
  have he : P.comap (algebraMap R S)=IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hc
  exact Ideal.map_le_iff_le_comap.mpr he.symm.le
/-- In the ACTUAL reduced closed fiber,base maximal parameters generate
each actual source maximal ideal after localization. LOCAL CM and local
dimension are explicit here;no global CM on the original variety is added. -/
theorem finite_reduced_fiber_parameters_regular_at_maximal
    {R S : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S]
    [IsReduced (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))]
    (rs : List R) (hgen : Ideal.ofList rs=IsLocalRing.maximalIdeal R)
    (P : Ideal S) [P.IsMaximal]
    [IsCohenMacaulayLocalRing (Localization.AtPrime P)]
    (hlen : (rs.length : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime P)) :
    IsRegular (Localization.AtPrime P)
      ((rs.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime P))) := by
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let I := Ideal.ofList (rs.map (algebraMap R S))
  have hI : I=(IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
    dsimp only [I]
    rw [← Ideal.map_ofList,hgen]
  letI : IsArtinianRing (S ⧸ I) := by
    rw [hI]
    exact finite_algebra_closed_fiber_artinian (R:=R) (S:=S)
  letI : IsReduced (S ⧸ I) := by rw [hI];infer_instance
  have hIP : I ≤ P := hI.le.trans (finite_algebra_maximal_contains_base_maximal P)
  have hloc : Ideal.ofList
      ((rs.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime P)))=
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← Ideal.map_ofList]
    exact artinian_reduced_cut_local_ideal_eq_maximalIdeal_of_le I P hIP
  apply isRegular_of_maximalIdeal_mem_ofList_minimalPrimes
  · rw [hloc,Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  · simpa only [List.length_map] using hlen
/-- A LOCAL finite reduced fiber and pointwise LOCAL CM/dimension derive
freeness;the free/flat conclusion is not an input. Instantiation of the
actual original geometric charts remains a separate obligation. -/
theorem finite_free_of_reduced_fiber_local_parameters
    {R S : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S]
    [IsReduced (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))]
    [∀ (P : Ideal S) [P.IsMaximal],IsCohenMacaulayLocalRing (Localization.AtPrime P)]
    (rs : List R) (hgen : Ideal.ofList rs=IsLocalRing.maximalIdeal R)
    (hlen : ∀ (P : Ideal S) [P.IsMaximal],
      (rs.length : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime P)) :
    Module.Free R S := by
  apply finite_free_of_maximal_local_regular_parameters rs hgen
  intro P hP
  exact (finite_reduced_fiber_parameters_regular_at_maximal rs hgen P (hlen P)).1
end LinearStudy
