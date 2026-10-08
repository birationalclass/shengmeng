module
public import Linear.PolynomialReindexResiduePairing
public import Linear.PolynomialReducedPointCount
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
namespace LinearStudy
attribute [local instance] Fintype.ofFinite
variable {K σ : Type*} [Field K] [IsAlgClosed K]

/-- The chosen actual residue maps construct an equivalence with the
actual polynomial zero locus. No reducedness is required. -/
def polynomialMaximalPointEquiv (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (q : MaximalSpectrum (MvPolynomial σ K ⧸ I) →
      (MvPolynomial σ K ⧸ I) →ₐ[K] K)
    (hq : ∀ j, RingHom.ker (q j).toRingHom = j.asIdeal) :
    MaximalSpectrum (MvPolynomial σ K ⧸ I) ≃ MvPolynomial.zeroLocus K I := by
  classical
  let e := polynomialZeroLocusPointEquiv I
  let p := fun j => e.symm (q j)
  have hinj : Function.Injective p := by
    intro i j hij
    have hqeq : q i = q j := e.symm.injective hij
    apply MaximalSpectrum.ext
    rw [← hq i,← hq j,hqeq]
  have hsurj : Function.Surjective p := by
    intro x
    let φ := e x
    let j : MaximalSpectrum (MvPolynomial σ K ⧸ I) :=
      ⟨RingHom.ker φ.toRingHom,RingHom.ker_isMaximal_of_surjective φ.toRingHom (by
        intro a
        exact ⟨algebraMap K _ a,by simp⟩)⟩
    have hφ : q j = φ := scalarAlgHom_eq_of_kernel_eq (q j) φ (hq j)
    refine ⟨j,?_⟩
    change e.symm (q j) = x
    rw [hφ]
    exact e.symm_apply_apply x
  exact Equiv.ofBijective p ⟨hinj,hsurj⟩

theorem polynomialMaximalPointEquiv_evaluation (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (q : MaximalSpectrum (MvPolynomial σ K ⧸ I) →
      (MvPolynomial σ K ⧸ I) →ₐ[K] K)
    (hq : ∀ j, RingHom.ker (q j).toRingHom = j.asIdeal)
    (j : MaximalSpectrum (MvPolynomial σ K ⧸ I)) (F : MvPolynomial σ K) :
    MvPolynomial.eval (polynomialMaximalPointEquiv I q hq j).val F =
      q j (Ideal.Quotient.mk I F) := by
  have h := AlgHom.congr_fun
    ((polynomialZeroLocusPointEquiv I).apply_symm_apply (q j)) (Ideal.Quotient.mk I F)
  exact h

/-- Low-degree residue relation on the ACTUAL point set of a possibly
nonreduced equation algebra. All weights are nonzero and are constructed.
Highest-system and nilradical annihilator hypotheses remain explicit. -/
theorem polynomial_zeroLocus_weighted_relation [CharZero K] {n q : ℕ}
    (e : σ ≃ Fin (n+1)) (P : σ → MvPolynomial σ K)
    (hq : 0 < q) (hle : ∀ i, (P i).totalDegree ≤ q)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent q (P i)))) = {0})
    (Θ : MvPolynomial σ K)
    [Module.Finite K (MvPolynomial σ K ⧸ Ideal.span (Set.range P))]
    (hgen : let I := Ideal.span (Set.range P)
      (nilradical (MvPolynomial σ K ⧸ I)).annihilator =
        Ideal.span {Ideal.Quotient.mk I Θ}) :
    let I := Ideal.span (Set.range P)
    letI : Fintype (MvPolynomial.zeroLocus K I) :=
      (polynomial_zeroLocus_finite_of_module_finite I).fintype
    ∃ lam : MvPolynomial.zeroLocus K I → K, (∀ x, lam x ≠ 0) ∧
      ∀ F : MvPolynomial σ K, Θ.totalDegree + F.totalDegree < (n+1)*(q-1) →
        ∑ x : MvPolynomial.zeroLocus K I, lam x * MvPolynomial.eval x.val F = 0 := by
  classical
  intro I
  letI : Fintype (MvPolynomial.zeroLocus K I) :=
    (polynomial_zeroLocus_finite_of_module_finite I).fintype
  let A := MvPolynomial σ K ⧸ I
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite K A
  obtain ⟨p,hv⟩ := polynomial_reindexed_low_degree_pairing e P hq hle hz
  obtain ⟨qA,hqA⟩ := finiteAlgebra_exists_maximal_residue_evaluations (K := K) (A := A)
  obtain ⟨lam,hlam,hsum⟩ := perfect_nilradical_socle_weighted_evaluation qA hqA p
    (Ideal.Quotient.mk I Θ) hgen
  let E := polynomialMaximalPointEquiv I qA hqA
  refine ⟨fun x => lam (E.symm x),fun x => hlam _,?_⟩
  intro F hF
  have hprod : (F*Θ).totalDegree < (n+1)*(q-1) :=
    (MvPolynomial.totalDegree_mul F Θ).trans_lt (by simpa only [add_comm] using hF)
  have hh := hv (F*Θ) hprod
  rw [map_mul,hsum] at hh
  rw [← E.sum_comp (fun x => lam (E.symm x) * MvPolynomial.eval x.val F)]
  simp only [E.symm_apply_apply]
  convert hh using 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a => lam j * a) (polynomialMaximalPointEquiv_evaluation I qA hqA j F)

end LinearStudy
