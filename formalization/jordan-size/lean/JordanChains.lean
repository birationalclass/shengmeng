import JordanProfiles
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JordanSize
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A Jordan chain, indexed from its eigenvector endpoint. -/
structure JordanChain (T : Module.End K V) (a : K) (r : ℕ) where
  vectors : Fin r → V
  independent : LinearIndependent K vectors
  relation : ∀ i : Fin r, (T-a • 1) (vectors i) =
    if h : i.val = 0 then 0 else vectors ⟨i.val-1, by omega⟩

lemma orbit_independent (D : Module.End K V) (r : ℕ) (x : V)
    (hzero : (D^r) x = 0) (htop : (D^(r-1)) x ≠ 0) :
    LinearIndependent K (fun i : Fin r => (D^i.val) x) := by
  induction r generalizing x with
  | zero => exact linearIndependent_empty_type
  | succ r ih =>
    rw [linearIndependent_finSucc]
    constructor
    · by_cases hr : r=0
      · subst r; exact linearIndependent_empty_type
      · have hz : (D^r) (D x) = 0 := by
          simpa [pow_succ, Module.End.mul_apply] using hzero
        have ht : (D^(r-1)) (D x) ≠ 0 := by
          simpa [← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel
            (show 1 ≤ r by omega)] using htop
        change LinearIndependent K (fun i : Fin r => (D^(i.val+1)) x)
        simpa only [pow_succ, Module.End.mul_apply] using ih (D x) hz ht
    · intro hx
      have hs : Submodule.span K (Set.range
          (Fin.tail (fun i : Fin (r+1) => (D^i.val) x))) ≤ LinearMap.ker (D^r) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        change (D^r) ((D^(i.val+1)) x) = 0
        rw [← Module.End.mul_apply, ← pow_add]
        have he : r+(i.val+1) = i.val+(r+1) := by omega
        rw [he, pow_add, Module.End.mul_apply, hzero, map_zero]
      have hx' := hs hx
      exact htop (by simpa [LinearMap.mem_ker] using hx')

def chainFromGenerator (T : Module.End K V) (a : K) (r : ℕ) (x : V)
    (hzero : ((T-a • 1)^r) x = 0)
    (htop : ((T-a • 1)^(r-1)) x ≠ 0) : JordanChain T a r where
  vectors i := ((T-a • 1)^(r-1-i.val)) x
  independent := by
    have hi := orbit_independent (T-a • 1) r x hzero htop
    have hinj : Function.Injective (fun i : Fin r => (⟨r-1-i.val, by omega⟩ : Fin r)) := by
      intro i j h
      apply Fin.ext
      have he := congrArg Fin.val h
      dsimp at he
      omega
    exact hi.comp (fun i : Fin r => ⟨r-1-i.val, by omega⟩) hinj
  relation i := by
    split_ifs with h
    · have he : r-1-i.val+1=r := by omega
      rw [← Module.End.mul_apply, ← pow_succ', he, hzero]
    · have he : r-1-(i.val-1)=r-1-i.val+1 := by omega
      change (T-a • 1) (((T-a • 1)^(r-1-i.val)) x) =
        ((T-a • 1)^(r-1-(i.val-1))) x
      rw [← Module.End.mul_apply, ← pow_succ', he]

lemma chain_powers {r : ℕ} (T : Module.End K V) (a : K)
    (v : Fin (r+1) → V)
    (hrel : ∀ i : Fin (r+1), (T-a • 1) (v i) =
      if h : i.val = 0 then 0 else v ⟨i.val-1, by omega⟩)
    (i : Fin (r+1)) :
    ((T-a • 1)^(i.val+1)) (v i) = 0 ∧
    ((T-a • 1)^i.val) (v i) = v ⟨0, by omega⟩ := by
  induction i using Fin.induction with
  | zero => simpa using hrel 0
  | succ i ih =>
    have hr : (T-a • 1) (v i.succ) = v i.castSucc := by
      have hr' := hrel i.succ
      rw [dif_neg (by simp)] at hr'
      convert hr' using 1
      congr 1
    change ((T-a • 1)^(i.val+1)) (v i.castSucc) = 0 ∧
      ((T-a • 1)^i.val) (v i.castSucc) = v ⟨0, by omega⟩ at ih
    constructor
    · rw [Fin.val_succ, pow_succ, Module.End.mul_apply, hr]
      exact ih.1
    · rw [Fin.val_succ, pow_succ, Module.End.mul_apply, hr]
      exact ih.2

lemma JordanChain.endpoint_ne_zero {T : Module.End K V} {a : K}
    {r : ℕ} (C : JordanChain T a (r+1)) :
    C.vectors 0 ≠ 0 := C.independent.ne_zero 0

lemma JordanChain.top_powers {T : Module.End K V} {a : K}
    {r : ℕ} (C : JordanChain T a (r+1)) :
    ((T-a • 1)^(r+1)) (C.vectors (Fin.last r)) = 0 ∧
    ((T-a • 1)^r) (C.vectors (Fin.last r)) = C.vectors 0 := by
  exact chain_powers T a C.vectors C.relation (Fin.last r)

lemma chainRelations_independent {r : ℕ} (T : Module.End K V) (a : K)
    (v : Fin (r+1) → V) (hne : v 0 ≠ 0)
    (hrel : ∀ i : Fin (r+1), (T-a • 1) (v i) =
      if h : i.val = 0 then 0 else v ⟨i.val-1, by omega⟩) :
    LinearIndependent K v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  by_contra hi
  let support := Finset.univ.filter (fun j => g j ≠ 0)
  have hnon : support.Nonempty := ⟨i, by simp [support, hi]⟩
  let m := support.max' hnon
  have hm : m ∈ support := support.max'_mem hnon
  have hgm : g m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hpow : ∀ j : Fin (r+1), j ≤ m →
      ((T-a • 1)^m.val) (v j) = if j=m then v 0 else 0 := by
    intro j hj
    by_cases he : j=m
    · subst j; simpa using (chain_powers T a v hrel m).2
    · have hz := (chain_powers T a v hrel j).1
      have hn : j.val+1 ≤ m.val := by
        have := Fin.le_iff_val_le_val.mp hj
        have : j.val ≠ m.val := fun h => he (Fin.ext h)
        omega
      have hex : m.val=(m.val-(j.val+1))+(j.val+1) := by omega
      rw [hex, pow_add, Module.End.mul_apply, hz, map_zero, if_neg he]
  have he := congrArg (fun z => ((T-a • 1)^m.val) z) hg
  simp only [map_sum, map_smul, map_zero] at he
  have he' : g m • v 0 = 0 := by
    rw [Finset.sum_eq_single m] at he
    · simpa [hpow m le_rfl] using he
    · intro j _ hj
      by_cases hg' : g j=0
      · simp [hg']
      · have hjm : j ≤ m := support.le_max' _ (by simp [support, hg'])
        simp [hpow j hjm, hj]
    · simp
  exact smul_ne_zero hgm hne he'

end JordanSize
