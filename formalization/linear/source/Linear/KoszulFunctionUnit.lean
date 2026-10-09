module
public import Linear.KoszulUnitExactness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [CommRing R]

theorem functionKoszul_last_unit_exactAt {n : ℕ} (H : Fin (n+1) → R)
    (hunit : IsUnit (H (Fin.last n))) (j : ℕ) (hj : 0 < j) :
    (koszulComplex (Fintype.linearCombination R H)).ExactAt j := by
  let H' : Fin n → R := fun i => H i.castSucc
  have hl : List.ofFn H=List.ofFn H'++[H (Fin.last n)] := by
    simpa only [List.concat_eq_append] using List.ofFn_succ' H
  have h := HomologicalComplex.ExactAt.of_iso
    (koszul_append_unit_exactAt (Fintype.linearCombination R (List.ofFn H').get)
      (H (Fin.last n)) hunit j hj) (koszulComplex.ofListIsoOfEq hl).symm
  rw [koszul_ofFn] at h
  exact h

/-- Any unit among the original equations suffices for positive-degree
exactness of their ACTUAL exterior-power Koszul complex. Reindexing is
an actual linear equivalence; no exactness hypothesis is assumed. -/
theorem functionKoszul_unit_exactAt {n : ℕ} (H : Fin n → R)
    (i : Fin n) (hunit : IsUnit (H i)) (j : ℕ) (hj : 0 < j) :
    (koszulComplex (Fintype.linearCombination R H)).ExactAt j := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := Equiv.swap i (Fin.last n)
    let H' := H ∘ e
    let E := LinearEquiv.funCongrLeft R R e
    have he : (Fintype.linearCombination R H').comp E.toLinearMap=Fintype.linearCombination R H := by
      apply LinearMap.ext
      intro v
      change (∑ k : Fin (n+1), v (e k) • H (e k))=∑ k : Fin (n+1),v k • H k
      exact Equiv.sum_comp e (fun k => v k • H k)
    have hu : IsUnit (H' (Fin.last n)) := by
      simpa only [H',Function.comp_apply,e,Equiv.swap_apply_right] using hunit
    exact HomologicalComplex.ExactAt.of_iso (functionKoszul_last_unit_exactAt H' hu j hj)
      (koszulComplex.isoOfEquiv (Fintype.linearCombination R H) E (Fintype.linearCombination R H') he).symm

end LinearStudy
