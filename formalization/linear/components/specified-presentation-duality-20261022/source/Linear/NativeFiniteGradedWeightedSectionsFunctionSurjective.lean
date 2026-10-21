module
public import Linear.NativeWeightedAffineSectionsFunctionSurjective
public import Linear.NativeFiniteGradedChartSectionsSurjective
public import Linear.NativeProjectiveCechAffineIntersections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ n : ℕ,∀ d : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D d → c • x ∈ D ((n : ℤ)+d))
variable [IsNoetherianRing S] [Module.Finite S M]
private theorem chartSurjective_of_equal (d e : ℕ) (c z : S)
    (hc : c ∈ B d) (hz : z ∈ B e) (hd : d=e) (hcz : c=z)
    (hs : Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hD d c hc)) :
    Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hD e z hz) := by
  cases hd
  cases hcz
  exact hs
variable {ι : Type u} (a : ι → S) (ha : ∀ i,a i ∈ B 1)
variable (hgen : Algebra.adjoin K (Set.range a) = ⊤)
include a ha hgen
/-- For the ORIGINAL finite graded module over a Noetherian degree-one generated
ring,all weighted product-chart section maps are surjective.The one-chart
surjectivity and ACTUAL QC are DERIVED;no domain/CM/torsion-free input. -/
theorem nativeFiniteGradedWeightedChartSectionMap_surjective
    (e : ℕ) (he : 0 < e) (c b : S) (hc : c ∈ B 1) (hb : b ∈ B e) :
    Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hD (1+e) (c*b)
      (SetLike.mul_mem_graded hc hb)) := by
  letI : (nativeProjectiveModuleSheaf B D hD 0).IsQuasicoherent :=
    nativeFiniteGraded_isQuasicoherent B D hD a ha hgen
  exact nativeWeightedChartSectionMap_surjective_of_actualChart_function B D hD e he c b hc hb
    (nativeFiniteGradedChartDegreeZeroSectionMap_surjective B D hD a ha hgen c hc)
/-- EVERY original finite Cech intersection has surjective original fraction
sections,including arbitrary torsion modules and zero coordinate products.
This is the missing ambient-side statement,with all finiteness/QC conditions
proved from the original graded module rather than section certificates. -/
theorem nativeFiniteGradedCechProductChartSectionMap_surjective
    (p : ℕ) (t : Fin (p+1) → ι) :
    Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hD (p+1)
      (∏ k : Fin (p+1),a (t k)) (nativeProjective_cechProduct_mem_degree B a ha p t)) := by
  cases p with
  | zero =>
    exact chartSurjective_of_equal B D hD 1 (0+1) (a (t 0)) _ (ha (t 0)) _ rfl
      (Fin.prod_univ_one (fun k : Fin (0+1) => a (t k))).symm
      (nativeFiniteGradedChartDegreeZeroSectionMap_surjective B D hD a ha hgen (a (t 0)) (ha (t 0)))
  | succ p =>
    let b := ∏ k : Fin (p+1),a (t k.succ)
    have hb : b ∈ B (p+1) := nativeProjective_cechProduct_mem_degree B a ha p (fun k => t k.succ)
    have H := nativeFiniteGradedWeightedChartSectionMap_surjective B D hD a ha hgen
      (p+1) (Nat.zero_lt_succ p) (a (t 0)) b (ha (t 0)) hb
    exact chartSurjective_of_equal B D hD (1+(p+1)) (p+1+1) (a (t 0)*b) _
      (SetLike.mul_mem_graded (ha (t 0)) hb) _ (by omega)
      (Fin.prod_univ_succ (fun k : Fin (p+1+1) => a (t k))).symm H
end LinearStudy
