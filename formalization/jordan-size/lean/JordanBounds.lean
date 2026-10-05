import LogarithmicFactors
noncomputable section
namespace JordanSize
variable {K V : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]
 [AddCommGroup V] [Module K V] [Module ℚ V] [IsScalarTower ℚ K V]
 [FiniteDimensional K V] {T : Module.End K V}

lemma Factors.shift_power (F : Factors T) (a : K) (x : V)
    (hx : x ∈ T.maxGenEigenspace a) (j : ℕ) :
    ((T-a • 1)^j) x = a^j • ((F.u-1)^j) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hc : Commute T (F.u-1) := by
      apply Commute.sub_right _ (Commute.one_right T)
      simpa only [F.factor] using F.commute.mul_left (Commute.refl F.u)
    have hy : ((F.u-1)^j) x ∈ T.maxGenEigenspace a :=
      Module.End.mapsTo_genEigenspace_of_comm (hc.pow_right j) a ⊤ hx
    have ht : T (((F.u-1)^j) x) = a • F.u (((F.u-1)^j) x) := by
      calc T (((F.u-1)^j) x) = (F.s*F.u) (((F.u-1)^j) x) :=
            congrArg (fun L : Module.End K V => L (((F.u-1)^j) x)) F.factor
           _ = a • F.u (((F.u-1)^j) x) := by
             rw [F.commute.eq, Module.End.mul_apply, F.s_apply hy, map_smul]
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih, map_smul,
      LinearMap.sub_apply, ht, LinearMap.smul_apply, Module.End.one_apply]
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      smul_sub, smul_smul, pow_succ]
    have hu : ((F.u-1)^j) (F.u x) = F.u (((F.u-1)^j) x) :=
      congrArg (fun L : Module.End K V => L x)
        (((Commute.refl F.u).sub_left (Commute.one_left F.u)).pow_left j).eq
    rw [map_sub, hu]
    module

/-- The largest Jordan block is characterized by the uniform annihilation
exponent on all generalized eigenspaces; no choice of Jordan basis is required. -/
def JordanBound (T : Module.End K V) (j : ℕ) : Prop :=
  ∀ a x, x ∈ T.maxGenEigenspace a → ((T-a • 1)^j) x = 0

lemma jordanBound_iff (F : Factors T) (j : ℕ) :
    JordanBound T j ↔ (F.u-1)^j = 0 := by
  constructor
  · intro h
    ext x
    have hx : x ∈ ⨆ a, T.maxGenEigenspace a := by
      rw [T.iSup_maxGenEigenspace_eq_top]; trivial
    refine Submodule.iSup_induction _ (motive := fun x => ((F.u-1)^j) x = 0)
      hx ?_ (by simp) ?_
    · intro a x hx
      by_cases ha : a=0
      · have hx0 : x=0 := (Module.End.isUnit_iff F.s).mp F.s_unit |>.1
          (by simpa [ha] using F.s_apply hx)
        simp [hx0]
      · have he := h a x hx
        rw [F.shift_power a x hx j] at he
        exact (smul_eq_zero.mp he).resolve_left (pow_ne_zero j ha)
    · intro x y hx hy; simp [map_add, hx, hy]
  · intro h a x hx
    rw [F.shift_power a x hx j, h]
    simp

lemma jordanBound_log_iff (F : Factors T) (j : ℕ) :
    JordanBound T j ↔ F.log^j = 0 := by
  rw [jordanBound_iff F]
  simpa only [F.exp_log] using (exponentialChains F.log F.log_nilpotent j).2.2
end JordanSize
#print axioms JordanSize.jordanBound_log_iff
