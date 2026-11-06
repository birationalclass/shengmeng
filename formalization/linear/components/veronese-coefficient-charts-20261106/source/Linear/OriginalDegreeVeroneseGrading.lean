module
public import Linear.OriginalDegreeVeroneseAlgebra
public import Mathlib.Algebra.DirectSum.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]

theorem originalDegreeVeronesePiece_independent (q : ℕ) (hq : 0 < q) :
    iSupIndep (originalDegreeVeronesePiece B q) := by
  have hB : iSupIndep B := (DirectSum.Decomposition.isInternal B).submodule_iSupIndep
  have hP : iSupIndep (fun n => B (q * n)) :=
    hB.comp (fun _ _ h => Nat.mul_left_cancel hq h)
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (originalDegreeVeronesePiece B q)).mpr
  intro s x hx hsum n hn
  let f := (originalDegreeVeroneseAlgebra B q).val.toLinearMap
  have hz : (∑ i ∈ s, f (x i)) = 0 := by
    simpa only [map_sum, map_zero] using congrArg f hsum
  apply Subtype.ext
  exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (fun i => B (q * i))).mp hP
    s (fun i => f (x i)) (fun i hi => hx i hi) hz n hn

theorem originalDegreeVeronesePiece_total (q : ℕ) :
    (⨆ n, originalDegreeVeronesePiece B q n) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  let V := originalDegreeVeroneseAlgebra B q
  let W : Submodule K V := ⨆ n, originalDegreeVeronesePiece B q n
  have hx : (x : S) ∈ ⨆ n, B (q * n) := x.property
  refine Submodule.iSup_induction' (fun n => B (q * n))
    (motive := fun a ha => (⟨a,ha⟩ : V) ∈ W) ?_ ?_ ?_ hx
  · intro n a ha
    exact Submodule.mem_iSup_of_mem n ha
  · exact W.zero_mem
  · intro a b ha hb h₁ h₂
    exact W.add_mem h₁ h₂

/-- The exact original degree-qn pieces are a grading of the Veronese
subalgebra when q is positive. -/
@[instance_reducible] def originalDegreeVeroneseGrading (q : ℕ) (hq : 0 < q) :
    GradedAlgebra (originalDegreeVeronesePiece B q) where
  __ := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (originalDegreeVeronesePiece_independent B q hq)
    (originalDegreeVeronesePiece_total B q)).chooseDecomposition
  one_mem := by
    change (1 : S) ∈ B (q * 0)
    simpa only [Nat.mul_zero] using SetLike.one_mem_graded B
  mul_mem := by
    intro i j a b ha hb
    change (a : S) * (b : S) ∈ B (q * (i + j))
    rw [Nat.mul_add]
    exact SetLike.mul_mem_graded ha hb

end LinearStudy
#check LinearStudy.originalDegreeVeronesePiece_independent
#print axioms LinearStudy.originalDegreeVeronesePiece_independent
#check LinearStudy.originalDegreeVeronesePiece_total
#print axioms LinearStudy.originalDegreeVeronesePiece_total
#check LinearStudy.originalDegreeVeroneseGrading
#print axioms LinearStudy.originalDegreeVeroneseGrading
