module
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Derivative
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R S ι : Type*} [CommRing R] [CommRing S]

def powerSeriesMapEquiv (e : R ≃+* S) :
    MvPowerSeries ι R ≃+* MvPowerSeries ι S where
  toFun := MvPowerSeries.map e.toRingHom
  invFun := MvPowerSeries.map e.symm.toRingHom
  left_inv := by
    intro f
    ext m
    simp only [MvPowerSeries.coeff_map]
    exact e.symm_apply_apply _
  right_inv := by
    intro f
    ext m
    simp only [MvPowerSeries.coeff_map]
    exact e.apply_symm_apply _
  map_add' := (MvPowerSeries.map e.toRingHom).map_add
  map_mul' := (MvPowerSeries.map e.toRingHom).map_mul

theorem powerSeriesMapEquiv_X (e : R ≃+* S) (i : ι) :
    powerSeriesMapEquiv e (MvPowerSeries.X i) = MvPowerSeries.X i := by
  exact MvPowerSeries.map_X e.toRingHom i

theorem powerSeriesMapEquiv_C (e : R ≃+* S) (a : R) :
    powerSeriesMapEquiv e (MvPowerSeries.C a : MvPowerSeries ι R) = MvPowerSeries.C (e a) := by
  exact MvPowerSeries.map_C e.toRingHom a

theorem powerSeriesMapEquiv_univariate_X (e : R ≃+* S) :
    powerSeriesMapEquiv e (PowerSeries.X : PowerSeries R) = PowerSeries.X := by
  change PowerSeries.map e.toRingHom PowerSeries.X = _
  exact PowerSeries.map_X e.toRingHom

theorem powerSeriesMapEquiv_univariate_C (e : R ≃+* S) (a : R) :
    powerSeriesMapEquiv e (PowerSeries.C a : PowerSeries R) = PowerSeries.C (e a) := by
  change PowerSeries.map e.toRingHom (PowerSeries.C a) = _
  exact PowerSeries.map_C e.toRingHom a

def nestedPowerSeriesEquiv (K : Type*) [CommRing K] (r : ℕ) :
    (c : ℕ) → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ≃+*
      MvPowerSeries (Fin (r + c)) K
  | 0 => (MvPowerSeries.isEmptyEquiv (Fin 0) (MvPowerSeries (Fin r) K)).toRingEquiv
  | c + 1 => by
    let e := nestedPowerSeriesEquiv K r c
    let ep : PowerSeries (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) ≃+*
        PowerSeries (MvPowerSeries (Fin (r + c)) K) := powerSeriesMapEquiv e
    let e' := (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c).toRingEquiv.trans
      (ep.trans (MvPowerSeries.finSuccEquiv K (r + c)).symm.toRingEquiv)
    exact e'

theorem finSucc_constantCoeff (K : Type*) [CommRing K] (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) K) :
    (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv K n f)).constantCoeff =
      f.constantCoeff := by
  have h := MvPowerSeries.coeff_coeff_finSuccEquiv (p := f) (k := 0) (x := 0)
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.cons_zero_zero] using h

theorem nestedPowerSeriesEquiv_constantCoeff
    (K : Type*) [CommRing K] (r c : ℕ)
    (f : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    (nestedPowerSeriesEquiv K r c f).constantCoeff = f.constantCoeff.constantCoeff := by
  induction c with
  | zero => rfl
  | succ c ih =>
    apply (finSucc_constantCoeff K (r + c) (nestedPowerSeriesEquiv K r (c + 1) f)).symm.trans
    change (PowerSeries.constantCoeff
      ((MvPowerSeries.finSuccEquiv K (r + c))
        ((MvPowerSeries.finSuccEquiv K (r + c)).symm
          (powerSeriesMapEquiv (nestedPowerSeriesEquiv K r c)
            (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c f))))).constantCoeff = _
    rw [AlgEquiv.apply_symm_apply]
    change (nestedPowerSeriesEquiv K r c
      (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c f))).constantCoeff = _
    rw [ih]
    rw [finSucc_constantCoeff]

def normalVariableIndex (r c : ℕ) (i : Fin c) : Fin (r + c) :=
  ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_add_left c r)⟩

theorem nestedPowerSeriesEquiv_X
    (K : Type*) [CommRing K] (r c : ℕ) (i : Fin c) :
    nestedPowerSeriesEquiv K r c (MvPowerSeries.X i) =
      MvPowerSeries.X (normalVariableIndex r c i) := by
  induction c with
  | zero => exact Fin.elim0 i
  | succ c ih =>
    induction i using Fin.cases with
    | zero =>
      change (MvPowerSeries.finSuccEquiv K (r + c)).symm
        (powerSeriesMapEquiv (nestedPowerSeriesEquiv K r c)
          (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c (MvPowerSeries.X 0))) = _
      rw [MvPowerSeries.finSuccEquiv_X_zero, powerSeriesMapEquiv_univariate_X]
      apply (MvPowerSeries.finSuccEquiv K (r + c)).injective
      simp [normalVariableIndex]
    | succ i =>
      change (MvPowerSeries.finSuccEquiv K (r + c)).symm
        (powerSeriesMapEquiv (nestedPowerSeriesEquiv K r c)
          (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c (MvPowerSeries.X i.succ))) = _
      rw [MvPowerSeries.finSuccEquiv_X_succ, powerSeriesMapEquiv_univariate_C, ih]
      have hi : normalVariableIndex r (c + 1) i.succ = (normalVariableIndex r c i).succ := by
        ext; rfl
      rw [hi]
      apply (MvPowerSeries.finSuccEquiv K (r + c)).injective
      simp

theorem finSuccEquiv_rename_succ (K : Type*) [CommRing K] (n : ℕ)
    (f : MvPowerSeries (Fin n) K) :
    MvPowerSeries.finSuccEquiv K n (MvPowerSeries.rename Fin.succ f) = PowerSeries.C f := by
  classical
  ext k d
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, PowerSeries.coeff_C]
  by_cases hk : k = 0
  · subst k
    simp only
    have hc : Finsupp.cons 0 d = Finsupp.embDomain (Fin.succEmb n) d := by
      ext i
      induction i using Fin.cases with
      | zero => simp [Finsupp.embDomain_of_notMem_range]
      | succ i =>
        rw [Finsupp.cons_succ]
        exact (Finsupp.embDomain_apply_self (Fin.succEmb n) d i).symm
    rw [hc]
    exact MvPowerSeries.coeff_embDomain_rename (Fin.succEmb n) f d
  · simp only [ite_eq_right hk, map_zero]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨b, hb⟩
    have hzero := Finsupp.mapDomain_of_notMem_range (f := Fin.succ) b (0 : Fin (n + 1))
      (by simp)
    rw [hb] at hzero
    simpa using hk hzero

theorem nestedPowerSeriesEquiv_C
    (K : Type*) [CommRing K] (r c : ℕ) (f : MvPowerSeries (Fin r) K) :
    nestedPowerSeriesEquiv K r c (MvPowerSeries.C f) =
      MvPowerSeries.rename (fun i : Fin r => i.addNat c) f := by
  induction c with
  | zero =>
    change f = MvPowerSeries.rename (fun i : Fin r => i.addNat 0) f
    change f = MvPowerSeries.rename id f
    exact (MvPowerSeries.rename_id_apply f).symm
  | succ c ih =>
    change (MvPowerSeries.finSuccEquiv K (r + c)).symm
      (powerSeriesMapEquiv (nestedPowerSeriesEquiv K r c)
        (MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin r) K) c (MvPowerSeries.C f))) = _
    rw [MvPowerSeries.finSuccEquiv_C, powerSeriesMapEquiv_univariate_C, ih]
    have hi : (fun i : Fin r => i.addNat (c + 1)) =
        Fin.succ ∘ (fun i : Fin r => i.addNat c) := by
      funext i; ext; simp [Fin.addNat]; omega
    rw [hi, ← MvPowerSeries.rename_comp_rename]
    apply (MvPowerSeries.finSuccEquiv K (r + c)).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (finSuccEquiv_rename_succ K (r + c)
      (MvPowerSeries.rename (fun i : Fin r => i.addNat c) f)).symm
end LinearStudy
