module
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Rename
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open scoped MvPowerSeries.WithPiTopology
variable {K σ : Type*} [CommRing K]

theorem continuous_powerSeries_pderiv [TopologicalSpace K] [IsTopologicalRing K] (i : σ) :
    Continuous (MvPowerSeries.pderiv (R := K) i) := by
  apply continuous_pi
  intro d
  change Continuous (fun f : MvPowerSeries σ K =>
    MvPowerSeries.coeff d (MvPowerSeries.pderiv i f))
  simp_rw [MvPowerSeries.coeff_pderiv]
  exact (MvPowerSeries.WithPiTopology.continuous_coeff K _).mul continuous_const

theorem powerSeries_pderiv_commutes_of_variables
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (e : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (he : Continuous e)
    (i : σ) (hi : ∀ j, MvPowerSeries.pderiv i (e (MvPowerSeries.X j)) =
      e (MvPowerSeries.pderiv i (MvPowerSeries.X j)))
    (f : MvPowerSeries σ K) :
    MvPowerSeries.pderiv i (e f) = e (MvPowerSeries.pderiv i f) := by
  have hd := continuous_powerSeries_pderiv (K := K) i
  have h := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries (R := K) (σ := σ)
  have hp : (fun f => MvPowerSeries.pderiv i (e f)) ∘
      MvPolynomial.toMvPowerSeries = (fun f => e (MvPowerSeries.pderiv i f)) ∘
      MvPolynomial.toMvPowerSeries := by
    funext p
    change MvPowerSeries.pderiv i (e (p : MvPowerSeries σ K)) =
      e (MvPowerSeries.pderiv i (p : MvPowerSeries σ K))
    induction p using MvPolynomial.induction_on with
    | C a =>
      have hc : e (MvPowerSeries.C a) = MvPowerSeries.C a := e.commutes a
      simp [MvPolynomial.coe_C, hc]
    | add p q hp hq => simp only [MvPolynomial.coe_add, map_add, hp, hq]
    | mul_X p j hp =>
      simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul,
        Derivation.leibniz, smul_eq_mul, map_add, hp, hi j]
  exact congr_fun (h.equalizer (hd.comp he) (he.comp hd) hp) f

theorem powerSeries_pderiv_rename_off_image {τ : Type*}
    (u : σ → τ) [Filter.TendstoCofinite u] (j : τ)
    (hj : j ∉ Set.range u) (f : MvPowerSeries σ K) :
    MvPowerSeries.pderiv j (MvPowerSeries.rename u f) = 0 := by
  classical
  ext d
  rw [MvPowerSeries.coeff_pderiv]
  have hc : MvPowerSeries.coeff (d + Finsupp.single j 1) (MvPowerSeries.rename u f) = 0 := by
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨b, hb⟩
    have hzero := Finsupp.mapDomain_of_notMem_range (f := u) b j hj
    rw [hb] at hzero
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hzero
    omega
  simp [hc]

theorem powerSeries_pderiv_rename_equiv {τ : Type*}
    (e : σ ≃ τ) (i : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.pderiv (e i) (MvPowerSeries.rename e f) =
      MvPowerSeries.rename e (MvPowerSeries.pderiv i f) := by
  classical
  ext d
  let m := Finsupp.equivMapDomain e.symm d
  have hd : Finsupp.embDomain e.toEmbedding m = d := by
    ext j
    obtain ⟨j, rfl⟩ := e.surjective j
    simpa only [m, Equiv.coe_toEmbedding, Finsupp.equivMapDomain_apply, Equiv.symm_symm]
      using Finsupp.embDomain_apply_self e.toEmbedding m j
  rw [← hd, MvPowerSeries.coeff_pderiv]
  have hs : Finsupp.embDomain e.toEmbedding m + Finsupp.single (e i) 1 =
      Finsupp.embDomain e.toEmbedding (m + Finsupp.single i 1) := by
    rw [Finsupp.embDomain_add, Finsupp.embDomain_single]
    simp only [Equiv.coe_toEmbedding]
  have hc₁ := MvPowerSeries.coeff_embDomain_rename e.toEmbedding f (m + Finsupp.single i 1)
  have hc₂ := MvPowerSeries.coeff_embDomain_rename e.toEmbedding (MvPowerSeries.pderiv i f) m
  have hv := Finsupp.embDomain_apply_self e.toEmbedding m i
  simp only [Equiv.coe_toEmbedding] at hc₁ hc₂ hv
  rw [hs, hc₁, hc₂, MvPowerSeries.coeff_pderiv, hv]
end LinearStudy
