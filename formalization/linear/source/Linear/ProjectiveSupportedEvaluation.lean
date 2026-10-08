module
public import Linear.Evaluation
public import Linear.ProjectiveSimultaneousWholePointFibers
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- Extend an actual point-fiber relation by zero to the actual finite
union. This constructs the nonzero evaluation functional used at the
entrance to Section 4; it does not postulate a Koszul exact sequence. -/
theorem extend_point_relation_to_actual_superset {n t : ℕ}
    (S S₁ : Set (ProjectivePoint n)) (hS : S.Finite) (hS₁ : S₁.Finite)
    (hsub : S₁ ⊆ S) (hne : S₁.Nonempty)
    (v : S → CoordinateVector n)
    (lam : S₁ → ℂ) (hlam : ∀ x,lam x ≠ 0)
    (hrel : letI : Fintype S₁ := hS₁.fintype
      ∀ P : CoordinateRing n,P.IsHomogeneous t →
        ∑ x : S₁,lam x*MvPolynomial.eval (v ⟨x.val,hsub x.property⟩) P=0) :
    letI : Fintype S := hS.fintype
    ∃ weights : S → ℂ, weights ≠ 0 ∧
      (∀ x : S,x.val ∉ S₁ → weights x=0) ∧
      (∀ x : S,x.val ∈ S₁ → weights x ≠ 0) ∧
      weightedEvaluation weights ≠ 0 ∧
      ∀ P : MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ t,
        weightedEvaluation weights (homogeneousPointEvaluation t v P)=0 := by
  classical
  letI : Fintype S := hS.fintype
  letI : Fintype S₁ := hS₁.fintype
  let j : S₁ ↪ S := ⟨fun x => ⟨x.val,hsub x.property⟩,
    fun x y h => Subtype.ext (congrArg (fun z : S => z.val) h)⟩
  let weights : S → ℂ := fun x => if hx : x.val ∈ S₁ then lam ⟨x.val,hx⟩ else 0
  have hj (x : S₁) : weights (j x)=lam x := by
    change (if hx : x.val ∈ S₁ then lam ⟨x.val,hx⟩ else 0)=lam x
    simp [x.property]
  have hoff (x : S) (hx : x.val ∉ S₁) : weights x=0 := by simp [weights,hx]
  have hon (x : S) (hx : x.val ∈ S₁) : weights x ≠ 0 := by
    simpa [weights,hx] using hlam ⟨x.val,hx⟩
  have hweights : weights ≠ 0 := by
    obtain ⟨a,ha⟩ := hne
    intro hz
    have h := hj ⟨a,ha⟩
    rw [hz,Pi.zero_apply] at h
    exact hlam ⟨a,ha⟩ h.symm
  have hsum (u : S → ℂ) :
      (∑ x : S,weights x*u x)=∑ x : S₁,lam x*u (j x) := by
    calc
      _ = ∑ x ∈ Finset.univ.map j, weights x*u x := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hx
        have hxout : x.val ∉ S₁ := by
          intro hx₁
          apply hx
          exact Finset.mem_map.mpr ⟨⟨x.val,hx₁⟩,Finset.mem_univ _,Subtype.ext rfl⟩
        rw [hoff x hxout,zero_mul]
      _ = _ := by simp only [Finset.sum_map,hj]
  refine ⟨weights,hweights,hoff,hon,weightedEvaluation_nonzero weights hweights,?_⟩
  intro P
  rw [weightedEvaluation_apply]
  simp only [homogeneousPointEvaluation_apply]
  rw [hsum]
  exact hrel P.val P.property

end LinearStudy
