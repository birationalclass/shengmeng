import LogarithmicFactors
noncomputable section
namespace JordanSize
variable {A : Type*} [Ring A] [Algebra ℚ A]
lemma exp_nat (D : A) (hD : IsNilpotent D) (a : ℕ) :
    IsNilpotent.exp ((a : ℚ) • D) = (IsNilpotent.exp D)^a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.cast_add_one, add_smul, one_smul,
      IsNilpotent.exp_add_of_commute
        (((Commute.refl D).smul_left (a : ℚ))) (hD.smul _) hD, ih, pow_succ]

variable {K V : Type*} [Field K] [PerfectField K] [Algebra ℚ K]
 [AddCommGroup V] [Module K V] [Module ℚ V] [IsScalarTower ℚ K V] [FiniteDimensional K V]
 {T : Module.End K V}

lemma factors_unique (F G : Factors T) : F.s = G.s ∧ F.u = G.u := by
  have hs := Module.End.isNilpotent_isSemisimple_unique F.nilpotent_sub F.semisimple
    G.nilpotent_sub G.semisimple
    (F.commute_T_s.sub_left (Commute.refl F.s))
    (G.commute_T_s.sub_left (Commute.refl G.s)) (by abel)
  refine ⟨hs.2, ?_⟩
  apply F.s_unit.mul_left_cancel
  calc F.s * F.u = T := F.factor.symm
       _ = G.s * G.u := G.factor
       _ = F.s * G.u := by rw [hs.2]

def Factors.power (F : Factors T) (a : ℕ) : Factors (T^a) where
  s := F.s^a
  u := F.u^a
  semisimple := F.semisimple.pow a
  s_unit := F.s_unit.pow a
  u_unit := F.u_unit.pow a
  unipotent := by
    have h := (F.log_nilpotent.smul (a : ℚ)).isNilpotent_exp_sub_one
    rw [exp_nat F.log F.log_nilpotent, F.exp_log] at h
    exact h
  commute := F.commute.pow_pow a a
  factor := by simpa only [F.factor] using F.commute.mul_pow a

lemma Factors.log_power (F : Factors T) (a : ℕ) :
    (F.power a).log = (a : ℚ) • F.log := by
  apply nilpotent_exp_injective (F.power a).log_nilpotent (F.log_nilpotent.smul _)
  rw [(F.power a).exp_log, exp_nat F.log F.log_nilpotent, F.exp_log]
  rfl

lemma nonzero_smul_filtrations (D : Module.End K V) (a : ℚ) (ha : a ≠ 0) (j : ℕ) :
    LinearMap.ker ((a • D)^j) = LinearMap.ker (D^j) ∧
    LinearMap.range ((a • D)^j) = LinearMap.range (D^j) ∧
    ((a • D)^j = 0 ↔ D^j = 0) := by
  have hu : IsUnit (a • (1 : Module.End K V)) := by
    refine ⟨⟨a • 1, a⁻¹ • 1, ?_, ?_⟩, rfl⟩ <;> simp [smul_mul_smul_comm, ha]
  have h := unit_factor_filtrations D (a • 1) ((Commute.one_right D).smul_right a) hu j
  simpa only [mul_smul_comm, mul_one] using h
end JordanSize
#print axioms JordanSize.Factors.log_power
#print axioms JordanSize.nonzero_smul_filtrations
