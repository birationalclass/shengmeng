module
public import Linear.FiniteReducedAlgebraPoints
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace LinearStudy
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Extension preserves finite intersections of PAIRWISE COPRIME actual
ideals, by their product formula. No flatness assumption is introduced. -/
theorem ideal_map_iInf_of_pairwise_isCoprime
    (φ : R →+* S) {ι : Type*} [Finite ι] (I : ι → Ideal R)
    (hI : Pairwise (fun i j => IsCoprime (I i) (I j))) :
    (⨅ i, I i).map φ = ⨅ i, (I i).map φ := by
  classical
  letI : Fintype ι := Fintype.ofFinite _
  have hprod : ∏ i, I i = ⨅ i, I i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := I) (by intro i _ j _ hij; exact hI hij)
  have hmap : Pairwise (fun i j => IsCoprime ((I i).map φ) ((I j).map φ)) := by
    intro i j hij
    exact (hI hij).map (Ideal.mapHom φ)
  have hprodmap : ∏ i, (I i).map φ = ⨅ i, (I i).map φ := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := fun i => (I i).map φ)
      (by intro i _ j _ hij; exact hmap hij)
  calc
    (⨅ i, I i).map φ = (∏ i, I i).map φ := by rw [hprod]
    _ = ∏ i, (I i).map φ := map_prod (Ideal.mapHom φ) I Finset.univ
    _ = ⨅ i, (I i).map φ := hprodmap

/-- For an ACTUAL reduced Artinian target quotient, radicality of every
actual closed fiber implies radicality of the extended defining ideal.
This statement does not assume the conclusion or discard nilpotents. -/
theorem reducedArtinian_closed_baseChange_ideal_isRadical
    (φ : R →+* S) (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] [IsReduced (R ⧸ I)]
    (hfib : ∀ p : MaximalSpectrum (R ⧸ I),
      ((p.asIdeal.comap (Ideal.Quotient.mk I)).map φ).IsRadical) :
    (I.map φ).IsRadical := by
  classical
  let π := Ideal.Quotient.mk I
  let J (p : MaximalSpectrum (R ⧸ I)) := p.asIdeal.comap π
  have hzero : (⨅ p : MaximalSpectrum (R ⧸ I), p.asIdeal) = ⊥ := by
    rw [← IsArtinianRing.nilradical_eq_iInf, nilradical_eq_zero]
    rfl
  have hI : I = ⨅ p, J p := by
    rw [← Ideal.comap_iInf, hzero, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  let k (p : MaximalSpectrum (R ⧸ I)) : MaximalSpectrum R :=
    ⟨J p, by
      letI := p.isMaximal
      exact Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective⟩
  have hk : Function.Injective k := by
    intro p q hpq
    apply MaximalSpectrum.ext
    exact Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal hpq)
  have hpair : Pairwise (fun p q => IsCoprime (J p) (J q)) := by
    intro p q hpq
    exact MaximalSpectrum.isCoprime_of_ne (I := k p) (J := k q)
      (fun heq => hpq (hk heq))
  have hmap : I.map φ = ⨅ p, (J p).map φ :=
    (congrArg (fun H : Ideal R => H.map φ) hI).trans
      (ideal_map_iInf_of_pairwise_isCoprime φ J hpair)
  have hrad : (⨅ p, (J p).map φ).IsRadical :=
    Ideal.isRadical_iInf _ (fun p => hfib p)
  exact hmap.symm ▸ hrad

end LinearStudy
