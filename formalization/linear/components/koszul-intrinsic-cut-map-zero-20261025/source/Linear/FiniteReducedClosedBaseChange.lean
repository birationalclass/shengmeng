module
public import Linear.ReducedClosedBaseChange
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
variable {K R S : Type*} [CommRing K] [IsNoetherianRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]

/-- Finiteness of ALL actual closed fibers over a reduced Artinian
target quotient gives finiteness of its EXACT base-change quotient.
The proof embeds it in the finite product of the actual fiber quotients. -/
theorem reducedArtinian_closed_baseChange_quotient_finite
    (φ : R →ₐ[K] S) (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] [IsReduced (R ⧸ I)]
    (hfib : ∀ p : MaximalSpectrum (R ⧸ I),
      Module.Finite K (S ⧸ (p.asIdeal.comap (Ideal.Quotient.mk I)).map φ.toRingHom)) :
    Module.Finite K (S ⧸ I.map φ.toRingHom) := by
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
  have hmap : I.map φ.toRingHom = ⨅ p, (J p).map φ.toRingHom :=
    (congrArg (fun H : Ideal R => H.map φ.toRingHom) hI).trans
      (ideal_map_iInf_of_pairwise_isCoprime φ.toRingHom J hpair)
  let J' (p : MaximalSpectrum (R ⧸ I)) := (J p).map φ.toRingHom
  letI (p : MaximalSpectrum (R ⧸ I)) : Module.Finite K (S ⧸ J' p) := hfib p
  let q : S →ₐ[K] (Π p : MaximalSpectrum (R ⧸ I), S ⧸ J' p) :=
    AlgHom.pi (fun p => Ideal.Quotient.mkₐ K (J' p))
  have hq : ∀ s ∈ I.map φ.toRingHom, q s=0 := by
    intro s hs
    rw [hmap] at hs
    funext p
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.mem_iInf.mp hs) p)
  let e : (S ⧸ I.map φ.toRingHom) →ₐ[K]
      (Π p : MaximalSpectrum (R ⧸ I), S ⧸ J' p) :=
    Ideal.Quotient.liftₐ (I.map φ.toRingHom) q hq
  have he : Function.Injective e := by
    apply (injective_iff_map_eq_zero e).mpr
    intro a ha
    obtain ⟨s,rfl⟩ := Ideal.Quotient.mk_surjective a
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hmap]
    apply Ideal.mem_iInf.mpr
    intro p
    have hp := congrFun ha p
    change Ideal.Quotient.mk (J' p) s=0 at hp
    exact Ideal.Quotient.eq_zero_iff_mem.mp hp
  exact Module.Finite.of_injective e.toLinearMap he

end LinearStudy
