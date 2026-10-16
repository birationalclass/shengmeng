module

public import Linear.ArtinianGlobalPairing
public import Linear.PolynomialRegular
public import Linear.PolynomialFiberDiagonal
public import Linear.LocalResidueEvaluation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 300000
namespace LinearStudy
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem exists_maximalResidueMap [IsAlgClosed K] [Module.Finite K A]
    (p : MaximalSpectrum A) : ∃ q : A →ₐ[K] K, RingHom.ker q.toRingHom = p.asIdeal := by
  let : p.asIdeal.IsMaximal := p.isMaximal
  let : Field (A ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  let : Module.Finite K (A ⧸ p.asIdeal) := Module.Finite.quotient K p.asIdeal
  let e : K ≃ₐ[K] A ⧸ p.asIdeal := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ p.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let q := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K p.asIdeal)
  refine ⟨q, ?_⟩
  ext a
  change e.symm (Ideal.Quotient.mk p.asIdeal a) = 0 ↔ a ∈ p.asIdeal
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem polynomial_centered_coordinateIdeal_eq_eval_kernel (a : ι → K) :
    Ideal.span (Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (a i))) =
      RingHom.ker (MvPolynomial.aeval (R := K) a).toRingHom := by
  let u : MvPolynomial ι K →+* MvPolynomial ι K := RingHom.id _
  let v : MvPolynomial ι K →+* MvPolynomial ι K :=
    MvPolynomial.C.comp (MvPolynomial.aeval (R := K) a).toRingHom
  let pi := (MvPolynomial.aeval (R := K) a).toRingHom
  have hC : ∀ c, u (MvPolynomial.C c) = v (MvPolynomial.C c) := by simp [u, v]
  have hX : ∀ i, pi (u (MvPolynomial.X i)) = pi (v (MvPolynomial.X i)) := by
    simp [pi, u, v]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    simp
  · intro p hp
    obtain ⟨b, hb, _⟩ := polynomial_diagonal_difference u v pi hC hX p
    change MvPolynomial.aeval (R := K) a p = 0 at hp
    have hp' : MvPolynomial.eval a p = 0 := hp
    have he : p = ∑ i, b i * (MvPolynomial.X i - MvPolynomial.C (a i)) := by
      simpa [u, v, RingHom.comp_apply, hp'] using hb
    rw [he]
    apply Submodule.sum_mem
    intro i hi
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

theorem polynomial_quotient_coordinateIdeal_eq_kernel
    (P : ι → MvPolynomial ι K)
    (q : (MvPolynomial ι K ⧸ Ideal.span (Set.range P)) →ₐ[K] K) :
    let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
    let a := fun i => q (pi (MvPolynomial.X i))
    (Ideal.span (Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (a i)))).map pi =
      RingHom.ker q.toRingHom := by
  let pi := Ideal.Quotient.mkₐ K (Ideal.span (Set.range P))
  let a := fun i => q (pi (MvPolynomial.X i))
  have he : q.comp pi = MvPolynomial.aeval (R := K) a := by
    ext i
    simp [a]
  have hk : RingHom.ker (MvPolynomial.aeval (R := K) a).toRingHom =
      (RingHom.ker q.toRingHom).comap pi.toRingHom := by
    ext p
    change MvPolynomial.aeval (R := K) a p = 0 ↔ q (pi p) = 0
    rw [← he]
    rfl
  change (Ideal.span (Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (a i)))).map
    pi.toRingHom = _
  rw [polynomial_centered_coordinateIdeal_eq_eval_kernel a, hk]
  exact Ideal.map_comap_of_surjective pi.toRingHom Ideal.Quotient.mk_surjective _

theorem polynomial_quotient_kernel_socle
    {n : ℕ} (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hP : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) K) (List.ofFn P))
    [Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P))]
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P)) →ₐ[K] K) :
    ∃ delta : MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P),
      delta ≠ 0 ∧ (RingHom.ker q.toRingHom).annihilator = Ideal.span {delta} := by
  let R := MvPolynomial (Fin (n + 1)) K
  let I := Ideal.span (Set.range P)
  let Q := R ⧸ I
  let pi := Ideal.Quotient.mkₐ K I
  let a := fun i => q (pi (MvPolynomial.X i))
  let x : Fin (n + 1) → R := fun i => MvPolynomial.X i - MvPolynomial.C (a i)
  let u : R →+* R := RingHom.id _
  let v : R →+* R := MvPolynomial.C.comp (MvPolynomial.aeval (R := K) a).toRingHom
  let e := (MvPolynomial.aeval (R := K) a).toRingHom
  have hC : ∀ c, u (MvPolynomial.C c) = v (MvPolynomial.C c) := by
    intro c
    change MvPolynomial.C c = MvPolynomial.C (MvPolynomial.aeval (R := K) a (MvPolynomial.C c))
    simp
  have hX : ∀ i, e (u (MvPolynomial.X i)) = e (v (MvPolynomial.X i)) := by
    intro i
    change MvPolynomial.aeval (R := K) a (MvPolynomial.X i) =
      MvPolynomial.aeval (R := K) a (MvPolynomial.C (MvPolynomial.aeval (R := K) a (MvPolynomial.X i)))
    simp
  choose N hN _ using fun (i : Fin (n + 1)) => polynomial_diagonal_difference
    (R := K) (A := R) (B := K) u v e hC hX (P i)
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) R := N
  have he : q.comp pi = MvPolynomial.aeval (R := K) a := by
    ext i
    change q (pi (MvPolynomial.X i)) = MvPolynomial.aeval (R := K) a (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X]
  have hp0 (i : Fin (n + 1)) : MvPolynomial.aeval (R := K) a (P i) = 0 := by
    rw [← he]
    change q (pi (P i)) = 0
    have hp : pi (P i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))
    rw [hp, map_zero]
  have hm : M.mulVec x = P := by
    funext i
    have hh := hN i
    simp only [u, v, R, RingHom.comp_apply, RingHom.id_apply] at hh
    have hp' : MvPolynomial.eval a (P i) = 0 := hp0 i
    simpa [M, x, Matrix.mulVec, dotProduct, hp'] using hh.symm
  have hx := polynomial_centered_variables_regular (n + 1) a
  have hk := polynomial_quotient_coordinateIdeal_eq_kernel P q
  change (Ideal.span (Set.range x)).map (Ideal.Quotient.mk I) = RingHom.ker q.toRingHom at hk
  have hmax : ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk I)).IsMaximal := by
    rw [hk]
    exact RingHom.ker_isMaximal_of_surjective q.toRingHom
      (fun b => ⟨algebraMap K Q b, q.commutes b⟩)
  let : IsNoetherianRing Q := IsNoetherianRing.of_finite K Q
  let : IsArtinianRing Q := IsArtinianRing.of_finite K Q
  have hne := coefficientDeterminant_ne_zero_of_artinian_maximal P x hP hx M hm hmax
  refine ⟨Ideal.Quotient.mk I M.det, hne, ?_⟩
  rw [← hk]
  exact coordinate_annihilator_eq_coefficientDeterminant P x hP hx M hm

theorem polynomialQuotient_perfectPairing [IsAlgClosed K] [Infinite K]
    {n : ℕ} (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hP : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) K) (List.ofFn P))
    [Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P))] :
    Nonempty (PerfectMultiplicationPairing (B := K)
      (A := MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P))) := by
  let Q := MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P)
  let : IsNoetherianRing Q := IsNoetherianRing.of_finite K Q
  let : IsArtinianRing Q := IsArtinianRing.of_finite K Q
  choose q hq using fun j : MaximalSpectrum Q => exists_maximalResidueMap (K := K) j
  choose delta hdelta hgen using fun j : MaximalSpectrum Q => polynomial_quotient_kernel_socle P hP (q j)
  have hsoc : ∀ j, ∀ x : Q, x ∈ j.asIdeal.annihilator → ∃ b : K, x = b • delta j := by
    intro j x hx
    rw [← hq j] at hx
    exact kernel_socle_scalar_generation (q j) (delta j) (hgen j) x hx
  obtain ⟨p, _⟩ := exists_perfectPairing_of_global_scalar_socles delta hdelta hsoc
  exact ⟨p⟩

end LinearStudy
