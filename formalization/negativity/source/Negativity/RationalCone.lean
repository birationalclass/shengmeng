module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open Set Finset

/-- The rational-open-cone ingredient in positive Cartier decomposition:
every point of an open subset of a finite real coordinate space lies in
the convex hull of rational points of that same open set. -/
theorem open_set_mem_convexHull_rational {ι : Type*} [Fintype ι]
    (U : Set (ι → ℝ)) (hU : IsOpen U) (x : ι → ℝ) (hx : x ∈ U) :
    x ∈ convexHull ℝ {y | y ∈ U ∧ ∀ i, ∃ q : ℚ, (q : ℝ) = y i} := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  choose lo hlo using fun i : ι => exists_rat_btwn (show x i - ε < x i by linarith)
  choose hi hhi using fun i : ι => exists_rat_btwn (show x i < x i + ε by linarith)
  let corners : Set (ι → ℝ) := Set.univ.pi (fun i => {(lo i : ℝ), (hi i : ℝ)})
  have hcorners : corners ⊆ {y | y ∈ U ∧ ∀ i, ∃ q : ℚ, (q : ℝ) = y i} := by
    intro y hy
    have hmem (i : ι) : y i = (lo i : ℝ) ∨ y i = (hi i : ℝ) := by
      simpa using hy i (Set.mem_univ i)
    refine ⟨hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro i
      rw [Real.dist_eq, abs_lt]
      rcases hmem i with he | he <;> rw [he] <;>
        obtain ⟨hl, hr⟩ := hlo i <;> obtain ⟨hl', hr'⟩ := hhi i <;> constructor <;> linarith
    · intro i
      rcases hmem i with he | he
      · exact ⟨lo i, he.symm⟩
      · exact ⟨hi i, he.symm⟩
  apply convexHull_mono hcorners
  apply mem_convexHull_pi
  intro i _
  rw [convexHull_pair, segment_eq_Icc (le_trans (hlo i).2.le (hhi i).1.le)]
  exact ⟨(hlo i).2.le, (hhi i).1.le⟩

/-- Extract a finite nonnegative real combination of genuine rational
points of the open set. This proves existence rather than assuming a
positive rational decomposition as an input. -/
theorem open_set_exists_rational_convex_combination {ι : Type*} [Fintype ι]
    (U : Set (ι → ℝ)) (hU : IsOpen U) (x : ι → ℝ) (hx : x ∈ U) :
    ∃ (J : Type) (_ : Fintype J) (w : J → ℝ) (q : J → ι → ℚ),
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j, (fun i => (q j i : ℝ)) ∈ U) ∧
      ∑ j, w j • (fun i => (q j i : ℝ)) = x := by
  classical
  obtain ⟨J, hJ, w, z, hw, hsum, hz, heq⟩ :=
    mem_convexHull_iff_exists_fintype.mp (open_set_mem_convexHull_rational U hU x hx)
  have : Fintype J := hJ
  choose q hq using fun j i => (hz j).2 i
  have he (j : J) : (fun i => (q j i : ℝ)) = z j := funext (hq j)
  refine ⟨J, hJ, w, q, hw, hsum, ?_, ?_⟩
  · intro j
    rw [he j]
    exact (hz j).1
  · simpa only [he] using heq

/-- Actual real extension of a rational coefficient matrix. -/
noncomputable def rationalCoefficientMap {ι κ : Type*} [Fintype ι]
    (M : ι → κ → ℚ) : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) where
  toFun x k := ∑ i, x i * (M i k : ℝ)
  map_add' x y := by
    ext k
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    ext k
    simp [mul_assoc, Finset.mul_sum]

/-- The open positive cone of an actual rational coefficient matrix has
a finite rational positive decomposition. In divisor applications the
matrix records prime coefficients of rational Cartier generators. -/
theorem positive_rational_coefficient_decomposition {ι κ : Type*}
    [Fintype ι] [Fintype κ] (M : ι → κ → ℚ) (x : ι → ℝ)
    (hx : ∀ k, 0 < rationalCoefficientMap M x k) :
    ∃ (J : Type) (_ : Fintype J) (w : J → ℝ) (q : J → ι → ℚ),
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j k, 0 < rationalCoefficientMap M (fun i => (q j i : ℝ)) k) ∧
      ∑ j, w j • rationalCoefficientMap M (fun i => (q j i : ℝ)) =
        rationalCoefficientMap M x := by
  let U : Set (ι → ℝ) := {z | ∀ k, 0 < rationalCoefficientMap M z k}
  have hU : IsOpen U := by
    have hEq : U = ⋂ k, {z | 0 < rationalCoefficientMap M z k} := by
      ext z
      simp [U]
    rw [hEq]
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_lt continuous_const
      ((continuous_apply k).comp (rationalCoefficientMap M).continuous_of_finiteDimensional)
  obtain ⟨J, hJ, w, q, hw, hsum, hq, heq⟩ :=
    open_set_exists_rational_convex_combination U hU x hx
  have : Fintype J := hJ
  refine ⟨J, hJ, w, q, hw, hsum, hq, ?_⟩
  have h := congrArg (rationalCoefficientMap M) heq
  simpa only [map_sum, map_smul] using h

/-- Every finite real vector has a rational parameterization preserving
all of its rational homogeneous linear equations. No kernel-spanning
or zero-coefficient preservation is assumed. -/
theorem rational_parameterization_preserves_zero {ι κ : Type*}
    [Fintype ι] (M : ι → κ → ℚ) (x : ι → ℝ) :
    ∃ (n : ℕ) (t : Fin n → ℝ) (q : Fin n → ι → ℚ),
      rationalCoefficientMap q t = x ∧
      (∀ k, rationalCoefficientMap M x k = 0 →
        ∀ j, ∑ i, q j i * M i k = 0) := by
  classical
  let W : Submodule ℚ ℝ := Submodule.span ℚ (Set.range x)
  have : FiniteDimensional ℚ W :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range x)
  let b := Module.finBasis ℚ W
  let v (i : ι) : W := ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩
  let q (j : Fin (Module.finrank ℚ W)) (i : ι) : ℚ := b.repr (v i) j
  let t (j : Fin (Module.finrank ℚ W)) : ℝ := (b j : ℝ)
  refine ⟨Module.finrank ℚ W, t, q, ?_, ?_⟩
  · ext i
    change (∑ j, t j * (q j i : ℝ)) = x i
    have h := congrArg (fun a : W => (a : ℝ)) (b.sum_repr (v i))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def] at h
    simpa [t, q, v, mul_comm] using h
  · intro k hk j
    have he : (∑ i, M i k • v i : W) = 0 := by
      apply Subtype.ext
      simpa [v, rationalCoefficientMap, Algebra.smul_def, mul_comm] using hk
    have h := congrArg (fun a : W => b.repr a j) he
    simpa [q, mul_comm] using h

/-- Scalar extension commutes with a rational coefficient map. -/
theorem rationalCoefficientMap_cast {ι κ : Type*} [Fintype ι]
    (M : ι → κ → ℚ) (q : ι → ℚ) :
    rationalCoefficientMap M (fun i => (q i : ℝ)) =
      fun k => ((∑ i, q i * M i k : ℚ) : ℝ) := by
  ext k
  simp [rationalCoefficientMap]

/-- Vanishing prime coefficients are preserved for every real parameter
in the constructed rational family. -/
theorem rationalCoefficientMap_comp_zero {ι κ τ : Type*}
    [Fintype ι] [Fintype τ] (M : ι → κ → ℚ) (Q : τ → ι → ℚ)
    (z : τ → ℝ) (k : κ) (hk : ∀ j, ∑ i, Q j i * M i k = 0) :
    rationalCoefficientMap M (rationalCoefficientMap Q z) k = 0 := by
  classical
  simp only [rationalCoefficientMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← Rat.cast_mul, ← Rat.cast_sum, hk,
    Rat.cast_zero, mul_zero]
  simp

/-- The full finite coefficient lemma for effective real Cartier
decomposition, including zero coefficients. Rational combinations are
effective and introduce no prime outside the original support. The
result is a theorem about finite coefficient families; identification
with actual Cartier and Weil divisors is a separate geometric step. -/
theorem effective_rational_coefficient_decomposition {ι κ : Type*}
    [Fintype ι] [Fintype κ] (M : ι → κ → ℚ) (x : ι → ℝ)
    (hx : ∀ k, 0 ≤ rationalCoefficientMap M x k) :
    ∃ (J : Type) (_ : Fintype J) (w : J → ℝ) (q : J → ι → ℚ),
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j k, 0 ≤ rationalCoefficientMap M (fun i => (q j i : ℝ)) k) ∧
      (∀ j k, rationalCoefficientMap M x k = 0 →
        rationalCoefficientMap M (fun i => (q j i : ℝ)) k = 0) ∧
      ∑ j, w j • (fun i => (q j i : ℝ)) = x := by
  classical
  obtain ⟨n, t, Q, hQt, hQzero⟩ := rational_parameterization_preserves_zero M x
  let P := {k : κ // 0 < rationalCoefficientMap M x k}
  let U : Set (Fin n → ℝ) :=
    {z | ∀ k : P, 0 < rationalCoefficientMap M (rationalCoefficientMap Q z) k.1}
  have hU : IsOpen U := by
    have hEq : U = ⋂ k : P,
        {z | 0 < rationalCoefficientMap M (rationalCoefficientMap Q z) k.1} := by
      ext z
      simp [U]
    rw [hEq]
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_lt continuous_const
      ((continuous_apply k.1).comp ((rationalCoefficientMap M).continuous_of_finiteDimensional.comp
        (rationalCoefficientMap Q).continuous_of_finiteDimensional))
  have ht : t ∈ U := by
    intro k
    rw [hQt]
    exact k.2
  obtain ⟨J, hJ, w, a, hw, hsum, ha, heq⟩ :=
    open_set_exists_rational_convex_combination U hU t ht
  have : Fintype J := hJ
  let q (j : J) (i : ι) : ℚ := ∑ p, a j p * Q p i
  have hq (j : J) : (fun i => (q j i : ℝ)) =
      rationalCoefficientMap Q (fun p => (a j p : ℝ)) := by
    rw [rationalCoefficientMap_cast]
  have hz (j : J) (k : κ) (hk : rationalCoefficientMap M x k = 0) :
      rationalCoefficientMap M (fun i => (q j i : ℝ)) k = 0 := by
    rw [hq]
    exact rationalCoefficientMap_comp_zero M Q _ k (hQzero k hk)
  refine ⟨J, hJ, w, q, hw, hsum, ?_, hz, ?_⟩
  · intro j k
    by_cases hk : rationalCoefficientMap M x k = 0
    · rw [hz j k hk]
    · rw [hq]
      exact (ha j ⟨k, lt_of_le_of_ne (hx k) (Ne.symm hk)⟩).le
  · simp_rw [hq]
    have h := congrArg (rationalCoefficientMap Q) heq
    simpa only [map_sum, map_smul, hQt] using h

/-- Clearing denominators with a positive common integer multiplier. -/
theorem rational_vector_positive_integer_multiple {ι : Type*} [Fintype ι]
    (q : ι → ℚ) :
    ∃ (N : ℕ) (z : ι → ℤ), 0 < N ∧
      (fun i => (z i : ℝ)) = (N : ℝ) • (fun i => (q i : ℝ)) := by
  classical
  let N : ℕ := ∏ i, (q i).den
  have hN : 0 < N := Finset.prod_pos (fun i _ => (q i).den_pos)
  have hd (i : ι) : (q i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  choose c hc using fun i => hd i
  refine ⟨N, fun i => (q i).num * (c i : ℤ), hN, ?_⟩
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  rw [Rat.cast_def, hc i, Nat.cast_mul]
  have hden : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
  field_simp

/-- Every effective real combination of a finite rational coefficient
family is a nonnegative real combination of integral combinations of
that same family. Zero prime coefficients remain zero throughout.
No effectivity or denominator-clearing premise is assumed. -/
theorem effective_integral_coefficient_decomposition {ι κ : Type*}
    [Fintype ι] [Fintype κ] (M : ι → κ → ℚ) (x : ι → ℝ)
    (hx : ∀ k, 0 ≤ rationalCoefficientMap M x k) :
    ∃ (J : Type) (_ : Fintype J) (w : J → ℝ) (z : J → ι → ℤ),
      (∀ j, 0 ≤ w j) ∧
      (∀ j k, 0 ≤ rationalCoefficientMap M (fun i => (z j i : ℝ)) k) ∧
      (∀ j k, rationalCoefficientMap M x k = 0 →
        rationalCoefficientMap M (fun i => (z j i : ℝ)) k = 0) ∧
      ∑ j, w j • (fun i => (z j i : ℝ)) = x := by
  classical
  obtain ⟨J, hJ, w, q, hw, _, hq, hz, heq⟩ :=
    effective_rational_coefficient_decomposition M x hx
  have : Fintype J := hJ
  choose N z hN hNz using fun j => rational_vector_positive_integer_multiple (q j)
  have hNr (j : J) : (0 : ℝ) < N j := by exact_mod_cast hN j
  refine ⟨J, hJ, fun j => w j / N j, z, ?_, ?_, ?_, ?_⟩
  · intro j
    exact div_nonneg (hw j) (hNr j).le
  · intro j k
    rw [hNz j, map_smul]
    exact mul_nonneg (hNr j).le (hq j k)
  · intro j k hk
    rw [hNz j, map_smul, Pi.smul_apply, hz j k hk]
    simp
  · have hs (j : J) : (w j / (N j : ℝ)) • (fun i => (z j i : ℝ)) =
        w j • (fun i => (q j i : ℝ)) := by
      rw [hNz j, smul_smul, div_mul_cancel₀ _ (hNr j).ne']
    simpa only [hs] using heq

end Negativity
