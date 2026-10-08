module
public import Linear.MatrixPolynomialHighest
public import Linear.CompletionQuotient
public import Linear.AffinePointRelation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
variable {K σ τ : Type*} [Field K]

/-- Transport an actual multiplication pairing through an actual algebra
equivalence. Neither pairing perfection nor multiplication is assumed on
the target algebra. -/
def perfectMultiplicationPairingTransport
    {A B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (p : PerfectMultiplicationPairing (B := K) (A := A)) :
    PerfectMultiplicationPairing (B := K) (A := B) where
  functional := p.functional.comp e.symm.toLinearMap
  equiv := (e.symm.toLinearEquiv.trans p.equiv).trans e.symm.toLinearEquiv.dualMap
  equiv_apply := by
    intro x a
    simp only [LinearEquiv.trans_apply,LinearEquiv.dualMap_apply]
    change p.equiv (e.symm x) (e.symm a) = p.functional (e.symm (x*a))
    calc
      p.equiv (e.symm x) (e.symm a) = p.functional (e.symm x * e.symm a) :=
        p.equiv_apply _ _
      _ = p.functional (e.symm (x*a)) :=
        congrArg p.functional (map_mul e.symm x a).symm

theorem polynomial_reindex_equations_ideal (e : σ ≃ τ)
    (P : σ → MvPolynomial σ K) :
    Ideal.span (Set.range (fun i => MvPolynomial.renameEquiv K e (P (e.symm i)))) =
      (Ideal.span (Set.range P)).map (MvPolynomial.renameEquiv K e).toRingHom := by
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨P (e.symm i),Set.mem_range_self _,rfl⟩
  · rintro ⟨F,⟨i,rfl⟩,rfl⟩
    exact ⟨e i,by simp⟩

/-- Variable reindexing preserves the origin-only highest system. -/
theorem polynomial_reindex_highest_origin (e : σ ≃ τ)
    (P : σ → MvPolynomial σ K) (q : ℕ)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent q (P i)))) = {0}) :
    MvPolynomial.zeroLocus K (Ideal.span (Set.range (fun i =>
      MvPolynomial.homogeneousComponent q (MvPolynomial.renameEquiv K e (P (e.symm i)))))) = {0} := by
  have ht : (fun i => MvPolynomial.homogeneousComponent q
      (MvPolynomial.renameEquiv K e (P (e.symm i)))) =
      (fun i => MvPolynomial.renameEquiv K e (MvPolynomial.homogeneousComponent q (P (e.symm i)))) := by
    funext i
    exact (MvPolynomial.rename_homogeneousComponent (φ := e) q (P (e.symm i))).symm
  rw [ht,polynomial_reindex_equations_ideal e
    (fun i => MvPolynomial.homogeneousComponent q (P i))]
  apply polynomial_coordinate_origin_zeroLocus _ _ _ hz
  intro j
  simp [MvPolynomial.renameEquiv]

/-- Actual finite reindexing constructs the exact-q regular highest system
required by the existing residue API. -/
theorem polynomial_reindex_exact_highest [IsAlgClosed K] {n q : ℕ}
    (e : σ ≃ Fin n) (P : σ → MvPolynomial σ K)
    (hle : ∀ i, (P i).totalDegree ≤ q)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent q (P i)))) = {0}) :
    let P' := fun i => MvPolynomial.renameEquiv K e (P (e.symm i))
    (∀ i, (P' i).totalDegree = q) ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) K) (List.ofFn
        (fun i => MvPolynomial.homogeneousComponent (P' i).totalDegree (P' i))) ∧
      MvPolynomial.zeroLocus K (Ideal.span (Set.range (fun i =>
        MvPolynomial.homogeneousComponent (P' i).totalDegree (P' i)))) = {0} := by
  intro P'
  have hle' (i : Fin n) : (P' i).totalDegree ≤ q := by
    change (MvPolynomial.renameEquiv K e (P (e.symm i))).totalDegree ≤ q
    rw [MvPolynomial.totalDegree_renameEquiv]
    exact hle _
  have hz' := polynomial_reindex_highest_origin e P q hz
  obtain ⟨hd,hreg⟩ := polynomial_equations_exact_degree_of_highest_zeroLocus P' hle' hz'
  exact ⟨hd,hreg,by simpa only [hd] using hz'⟩

/-- Exact-q low-degree vanishing on the original equation algebra, with
arbitrary finite variable names. The comparison is an actual quotient
algebra equivalence, not an identification of reduced point sets. -/
theorem polynomial_reindexed_low_degree_pairing
    [IsAlgClosed K] [CharZero K] {n q : ℕ}
    (e : σ ≃ Fin (n+1)) (P : σ → MvPolynomial σ K)
    (hq : 0 < q) (hle : ∀ i, (P i).totalDegree ≤ q)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent q (P i)))) = {0}) :
    let I := Ideal.span (Set.range P)
    let A := MvPolynomial σ K ⧸ I
    ∃ p : PerfectMultiplicationPairing (B := K) (A := A),
      ∀ F : MvPolynomial σ K, F.totalDegree < (n+1)*(q-1) →
        p.functional (Ideal.Quotient.mk I F) = 0 := by
  classical
  intro I A
  let E := MvPolynomial.renameEquiv K e
  let P' := fun i => E (P (e.symm i))
  let J := Ideal.span (Set.range P')
  let B := MvPolynomial (Fin (n+1)) K ⧸ J
  let eqv : A ≃ₐ[K] B :=
    Ideal.quotientEquivAlg I J E (polynomial_reindex_equations_ideal e P)
  obtain ⟨hd,hreg,hz'⟩ := polynomial_reindex_exact_highest e P hle hz
  have hd' : ∀ i, (P' i).totalDegree = q := hd
  obtain ⟨pB,hv,_⟩ := affine_polynomial_low_degree_trace_pairing P' (fun i => by rw [hd];exact hq) hreg hz'
  let pA := perfectMultiplicationPairingTransport eqv.symm pB
  refine ⟨pA,?_⟩
  intro F hF
  have hEF : (E F).totalDegree < ∑ i, ((P' i).totalDegree-1) := by
    simpa only [E,MvPolynomial.totalDegree_renameEquiv,hd',Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hF
  have hh := hv (E F) hEF
  change pB.functional (eqv (Ideal.Quotient.mk I F)) = 0
  change pB.functional (Ideal.Quotient.mk J (E F)) = 0
  exact hh

end LinearStudy
