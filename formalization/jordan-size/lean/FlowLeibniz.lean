import NilpotentFlow
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
namespace JordanSize
open Finset Polynomial
variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]

def scalarFlowPoly (D : Module.End ℚ V) (k : ℕ) (x : V) (l : V →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ i ∈ range k, C ((i.factorial : ℚ)⁻¹ * l ((D ^ i) x)) * X ^ i

lemma scalarFlowPoly_eval (D : Module.End ℚ V) (k : ℕ) (hk : D ^ k = 0)
    (x : V) (l : V →ₗ[ℚ] ℚ) (t : ℚ) :
    (scalarFlowPoly D k x l).eval t = l ((flow D t) x) := by
  have ht : (t • D) ^ k = 0 := by rw [smul_pow, hk, smul_zero]
  simp only [scalarFlowPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    flow, IsNilpotent.exp_eq_sum ht, LinearMap.sum_apply, map_sum,
    LinearMap.smul_apply, smul_pow, map_smul, smul_eq_mul]
  apply sum_congr rfl
  intro i hi
  ring

def bilinearFlowPoly (B : V →ₗ[ℚ] W →ₗ[ℚ] Z)
    (D : Module.End ℚ V) (E : Module.End ℚ W) (k : ℕ)
    (x : V) (y : W) (l : Z →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ i ∈ range k, ∑ j ∈ range k,
    C ((i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹ *
      l (B ((D ^ i) x) ((E ^ j) y))) * X ^ (i+j)

lemma bilinearFlowPoly_eval (B : V →ₗ[ℚ] W →ₗ[ℚ] Z)
    (D : Module.End ℚ V) (E : Module.End ℚ W) (k : ℕ)
    (hD : D ^ k = 0) (hE : E ^ k = 0)
    (x : V) (y : W) (l : Z →ₗ[ℚ] ℚ) (t : ℚ) :
    (bilinearFlowPoly B D E k x y l).eval t =
      l (B ((flow D t) x) ((flow E t) y)) := by
  have htD : (t • D) ^ k = 0 := by rw [smul_pow, hD, smul_zero]
  have htE : (t • E) ^ k = 0 := by rw [smul_pow, hE, smul_zero]
  simp only [bilinearFlowPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    flow, IsNilpotent.exp_eq_sum htD, IsNilpotent.exp_eq_sum htE,
    LinearMap.sum_apply, map_sum, map_smul, LinearMap.smul_apply,
    smul_pow, smul_eq_mul]
  simp_rw [mul_sum]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

lemma scalarFlowPoly_coeff_one (D : Module.End ℚ V) (k : ℕ) (hk : 1 < k)
    (x : V) (l : V →ₗ[ℚ] ℚ) :
    (scalarFlowPoly D k x l).coeff 1 = l (D x) := by
  simp only [scalarFlowPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  simp [hk]

lemma bilinearFlowPoly_coeff_one (B : V →ₗ[ℚ] W →ₗ[ℚ] Z)
    (D : Module.End ℚ V) (E : Module.End ℚ W) (k : ℕ) (hk : 1 < k)
    (x : V) (y : W) (l : Z →ₗ[ℚ] ℚ) :
    (bilinearFlowPoly B D E k x y l).coeff 1 =
      l (B (D x) y) + l (B x (E y)) := by
  simp only [bilinearFlowPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  have hinner : ∀ i ∈ range k,
      (∑ j ∈ range k, if 1 = i+j then
        (i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹ *
          l (B ((D ^ i) x) ((E ^ j) y)) else 0) =
      if i = 0 then l (B x (E y)) else if i = 1 then l (B (D x) y) else 0 := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i; simp [hk]
    by_cases hi1 : i = 1
    · subst i; simp [show 0 < k by omega]
    · have hsum : ∀ j, 1 ≠ i+j := by omega
      simp [hsum, hi0, hi1]
  rw [sum_congr rfl hinner]
  have hsplit : ∀ i : ℕ,
      (if i = 0 then l (B x (E y)) else if i = 1 then l (B (D x) y) else 0) =
      (if i = 0 then l (B x (E y)) else 0) +
        (if i = 1 then l (B (D x) y) else 0) := by
    intro i
    by_cases hi0 : i = 0
    · simp [hi0]
    · by_cases hi1 : i = 1 <;> simp [hi0, hi1]
  simp_rw [hsplit, sum_add_distrib]
  simp [hk, show 0 < k by omega, add_comm]

/-- Multiplicativity at integer parameters implies the Leibniz identity,
by polynomial identity and comparison of the coefficient of X. -/
theorem flowLeibniz (B : V →ₗ[ℚ] W →ₗ[ℚ] Z)
    (D : Module.End ℚ V) (E : Module.End ℚ W) (F : Module.End ℚ Z)
    (hD : IsNilpotent D) (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hB : ∀ x y, (flow F 1) (B x y) = B ((flow D 1) x) ((flow E 1) y))
    (x : V) (y : W) :
    F (B x y) = B (D x) y + B x (E y) := by
  have hn : ∀ m : ℕ, ((flow F 1)^m) (B x y) =
      B (((flow D 1)^m) x) (((flow E 1)^m) y) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hB,
        pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
  obtain ⟨p, hp⟩ := hD
  obtain ⟨q, hq⟩ := hE
  obtain ⟨r, hr⟩ := hF
  let k := p + q + r + 2
  have hk : 1 < k := by dsimp [k]; omega
  have hDk : D^k = 0 := pow_eq_zero_of_le (by dsimp [k]; omega) hp
  have hEk : E^k = 0 := pow_eq_zero_of_le (by dsimp [k]; omega) hq
  have hFk : F^k = 0 := pow_eq_zero_of_le (by dsimp [k]; omega) hr
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro l
  let P := scalarFlowPoly F k (B x y) l
  let Q := bilinearFlowPoly B D E k x y l
  have heval : ∀ m : ℕ, P.eval (m : ℚ) = Q.eval (m : ℚ) := by
    intro m
    rw [scalarFlowPoly_eval F k hFk, bilinearFlowPoly_eval B D E k hDk hEk,
      flow_nat F ⟨r, hr⟩ m, flow_nat D ⟨p, hp⟩ m, flow_nat E ⟨q, hq⟩ m, hn m]
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
    rintro t ⟨m, rfl⟩
    exact heval m
  have hcoeff := congrArg (fun P : ℚ[X] => P.coeff 1) hPQ
  rw [scalarFlowPoly_coeff_one F k hk,
    bilinearFlowPoly_coeff_one B D E k hk] at hcoeff
  simpa [map_sub, map_add] using sub_eq_zero.mpr hcoeff

end JordanSize
#print axioms JordanSize.flowLeibniz
