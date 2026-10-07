module
public import Linear.PowerSeriesThickeningRegular
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
open RingTheory.Sequence
variable {K : Type*} [Field K]
attribute [local instance] NoZeroDivisors.to_isDomain

theorem powerSeries_thickening_finite_free
    (r c : ℕ) (hr : 0 < r) (hc : 0 < c)
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))
    (e : ℕ) (he : 0 < e)
    (hupper : Ideal.span (Set.range H) ≤
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))))
    (hlower : (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c)
      (R := MvPowerSeries (Fin r) K)))) ^ e ≤ Ideal.span (Set.range H)) :
    Module.Free (MvPowerSeries (Fin r) K)
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ⧸ Ideal.span (Set.range H)) := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  let B := MvPowerSeries (Fin r) K
  let R := MvPowerSeries (Fin c) B
  let I := Ideal.span (Set.range H)
  let J : Ideal R := Ideal.span (Set.range MvPowerSeries.X)
  let P : Ideal R := Ideal.span (Set.range (fun i : Fin r => MvPowerSeries.C (MvPowerSeries.X i)))
  let rs := List.ofFn H
  let ps : List R := List.ofFn (fun i : Fin r => MvPowerSeries.C (MvPowerSeries.X i))
  let : IsCohenMacaulayLocalRing R := nestedPowerSeries_isCohenMacaulayLocalRing r c (by omega)
  have hrad : I.radical = J := powerSeries_thickening_radical I e he hupper hlower
  have hp : J.IsPrime := by
    dsimp only [J]
    rw [← powerSeries_constantCoeff_kernel]
    exact RingHom.ker_isPrime MvPowerSeries.constantCoeff
  have hmax : J ⊔ P = IsLocalRing.maximalIdeal R :=
    (nestedPowerSeries_maximalIdeal r c hr hc).symm
  have hradIP : (I ⊔ P).radical = IsLocalRing.maximalIdeal R := by
    calc
      (I ⊔ P).radical = (J ⊔ P).radical := by
        rw [Ideal.radical_sup (I := I) (J := P), Ideal.radical_sup (I := J) (J := P),
          hrad, hp.radical]
      _ = IsLocalRing.maximalIdeal R := by
        rw [hmax]
        exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical
  have hlist : Ideal.ofList (rs ++ ps) = I ⊔ P := by
    dsimp only [rs, ps]
    rw [Ideal.ofList_append, ideal_ofFn, ideal_ofFn]
  have hall : IsRegular R (rs ++ ps) := by
    apply isRegular_of_maximalIdeal_mem_ofList_minimalPrimes
    · rw [hlist, ← Ideal.radical_minimalPrimes, hradIP,
        Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    · rw [nestedPowerSeries_ringKrullDim r c (by omega)]
      simp [rs, ps, Nat.add_comm]
  let A := R ⧸ I
  let : Module.Finite B A := powerSeries_coordinateIdeal_power_quotient_finite I e hlower
  have hP : IsWeaklyRegular A (ps.map (Ideal.Quotient.mk I)) := by
    have h := (weaklyRegular_quotient_iff rs ps).mpr
      ((isWeaklyRegular_append_iff R rs ps).mp hall.1).2
    rw [show Ideal.ofList rs = I by simp [rs, I, Ideal.ofList, List.mem_ofFn, Set.range]] at h
    exact h
  apply free_of_regular_maximal_algebraMap (List.ofFn (MvPowerSeries.X (σ := Fin r) (R := K)))
  · change IsWeaklyRegular A ((List.ofFn (MvPowerSeries.X (σ := Fin r) (R := K))).map
      (algebraMap B A))
    have hBA (b : B) : algebraMap B A b = Ideal.Quotient.mk I (MvPowerSeries.C b) := by
      change Ideal.Quotient.mk I (algebraMap B R b) = _
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self]
      rfl
    have hfun : (fun i : Fin r => algebraMap B A (MvPowerSeries.X i)) =
        (fun i : Fin r => Ideal.Quotient.mk I (MvPowerSeries.C (MvPowerSeries.X i))) :=
      funext (fun i => hBA _)
    rw [List.map_ofFn]
    change IsWeaklyRegular A (List.ofFn (fun i : Fin r => algebraMap B A (MvPowerSeries.X i)))
    rw [hfun]
    simpa only [ps, List.map_ofFn, Function.comp_def] using hP
  · rw [show Ideal.ofList (List.ofFn (MvPowerSeries.X (σ := Fin r) (R := K))) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin r) (R := K))) by
      simp [Ideal.ofList, List.mem_ofFn, Set.range]]
    exact powerSeries_coordinateIdeal_eq_maximalIdeal

end LinearStudy
