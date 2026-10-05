import LogarithmicFactors
import Mathlib.Algebra.BigOperators.Fin
noncomputable section
universe u
namespace JordanSize
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

lemma log_fixed {V : Type*} [AddCommGroup V] [Module K V]
    [Module ℚ V] [IsScalarTower ℚ K V] {T : Module.End K V}
    (F : Factors T) {x : V} (hx : T x = x) : F.log x = 0 := by
  have hu : (F.u-1) x = 0 := by simpa using sub_eq_zero.mpr (F.fixed hx)
  have hp : ∀ i : ℕ, i ≠ 0 → ((F.u-1)^i) x = 0 := by
    intro i hi
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [pow_succ, Module.End.mul_apply, hu, map_zero]
  simp only [Factors.log, operatorLog, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases h : i=0
  · simp [h]
  · simp [h, hp i h]

theorem logarithm_multilinear (n : ℕ) {M : Fin n → Type u} {Z : Type u}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, Module ℚ (M i)] [∀ i, IsScalarTower ℚ K (M i)]
    [∀ i, FiniteDimensional K (M i)]
    [AddCommGroup Z] [Module K Z] [Module ℚ Z] [IsScalarTower ℚ K Z]
    [FiniteDimensional K Z]
    (B : MultilinearMap K M Z) (T : ∀ i, Module.End K (M i))
    (R : Module.End K Z) (FT : ∀ i, Factors (T i)) (FR : Factors R)
    (hB : ∀ x, R (B x) = B (fun i => T i (x i))) (x : ∀ i, M i) :
    FR.log (B x) = ∑ i, B (Function.update x i ((FT i).log (x i))) := by
  induction n generalizing Z with
  | zero =>
    have hx : (fun i => T i (x i)) = x := by funext i; exact Fin.elim0 i
    simpa using log_fixed FR (by simpa only [hx] using hB x)
  | succ n ih =>
    let eT : M (Fin.last n) ≃ₗ[K] M (Fin.last n) :=
      LinearEquiv.ofBijective (T (Fin.last n))
        ((Module.End.isUnit_iff _).mp (FT (Fin.last n)).T_unit)
    let eR : Z ≃ₗ[K] Z :=
      LinearEquiv.ofBijective R ((Module.End.isUnit_iff _).mp FR.T_unit)
    let e : (M (Fin.last n) →ₗ[K] Z) ≃ₗ[K] (M (Fin.last n) →ₗ[K] Z) := LinearEquiv.arrowCongr eT eR
    let A := e.toLinearMap
    have hA : IsUnit A := (Module.End.isUnit_iff A).mpr e.bijective
    let FA : Factors A := jordanFactors A hA
    have hcur : ∀ y, A (B.curryRight y) =
        B.curryRight (fun i => T i.castSucc (y i)) := by
      intro y
      ext z
      change R (B (Fin.snoc y (eT.symm z))) =
        B (Fin.snoc (fun i => T i.castSucc (y i)) z)
      rw [hB]
      congr 1
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [eT]
      · simp
    have heval : ∀ (L : M (Fin.last n) →ₗ[K] Z) z,
        R (evalBilinear L z) = evalBilinear (A L) (T (Fin.last n) z) := by
      intro L z
      change R (L z) = R (L (eT.symm (eT z)))
      rw [eT.symm_apply_apply]
    have h := logarithm_bilinear evalBilinear A (T (Fin.last n)) R
      FA (FT (Fin.last n)) FR heval (B.curryRight (Fin.init x)) (x (Fin.last n))
    change FR.log (B (Fin.snoc (Fin.init x) (x (Fin.last n)))) =
      (FA.log (B.curryRight (Fin.init x))) (x (Fin.last n)) +
      B (Fin.snoc (Fin.init x) ((FT (Fin.last n)).log (x (Fin.last n)))) at h
    rw [ih B.curryRight (fun i => T i.castSucc) A (fun i => FT i.castSucc) FA
      hcur (Fin.init x), LinearMap.sum_apply] at h
    simp only [MultilinearMap.curryRight_apply, Fin.snoc_update,
      Fin.snoc_init_self, ← Fin.update_snoc_last] at h
    rw [Fin.sum_univ_castSucc]
    have hlast : Function.update x (Fin.last n)
        ((FT (Fin.last n)).log (x (Fin.last n))) =
        Fin.snoc (Fin.init x) ((FT (Fin.last n)).log (x (Fin.last n))) := by
      conv_lhs => arg 1; rw [← Fin.snoc_init_self x]
      exact Fin.update_snoc_last _ _ _
    simpa only [Fin.init, hlast] using h
end JordanSize
#print axioms JordanSize.logarithm_multilinear
