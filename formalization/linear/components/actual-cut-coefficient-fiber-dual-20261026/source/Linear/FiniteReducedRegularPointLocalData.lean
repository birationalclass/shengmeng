module
public import Linear.PowerSeriesCohenMacaulay
public import Linear.FiniteReducedLocalCut
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open RingTheory.Sequence
/-- Derive LOCAL CM and dimension from the SAME regular equations of
an ACTUAL finite reduced cut. Reuse existing regular-generator CM theorem;
no CM or dimension hypothesis is added to the local ring. -/
theorem finite_reduced_regular_cut_point_local_data
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (rs : List A) (p : Ideal A) [p.IsPrime]
    [IsArtinianRing (A ⧸ Ideal.ofList rs)] [IsReduced (A ⧸ Ideal.ofList rs)]
    (hpoint : Ideal.ofList rs ≤ p)
    (hreg : IsRegular (Localization.AtPrime p)
      (rs.map (algebraMap A (Localization.AtPrime p)))) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
      (rs.length : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p) := by
  let L := Localization.AtPrime p
  let ls := rs.map (algebraMap A L)
  have hgen : Ideal.ofList ls=IsLocalRing.maximalIdeal L := by
    rw [← Ideal.map_ofList]
    exact artinian_reduced_cut_local_ideal_eq_maximalIdeal_of_le (Ideal.ofList rs) p hpoint
  refine ⟨localRing_CohenMacaulay_of_regular_maximal_generators ls hreg hgen,?_⟩
  have hh := Ideal.ofList_height_eq_length_of_isWeaklyRegular ls hreg.1
    (by rw [hgen];exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top)
  rw [hgen] at hh
  have hd : ringKrullDim L=(ls.length : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,hh]
    rfl
  simpa only [ls,List.length_map] using hd.symm
end LinearStudy
