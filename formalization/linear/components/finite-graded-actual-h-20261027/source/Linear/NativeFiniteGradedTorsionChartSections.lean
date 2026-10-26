module
public import Linear.NativeChartKernelQuotientInjective
public import Linear.NativeFiniteGradedIndependentCechSections
public import Linear.IntegerGradedFiniteFreeSurjection
public import Linear.NativeProjectiveChartInjectiveAll
public import Mathlib.Algebra.Module.Torsion.Pi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option diagnostics true
set_option diagnostics.threshold 100
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable [IsDomain S] [IsNoetherianRing S] [Module.Finite S M]
variable {κ ι : Type u} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
variable (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
attribute [local irreducible] nativeProjectiveChartDegreeZeroSectionMap nativeProjectiveModuleSheaf
include c hc hgenC
/-- Actual native chart injectivity for EVERY finite graded coefficient,
including torsion coefficients. An actual shifted free surjection and its
finite graded kernel replace the former torsion-free coefficient assumption.
The chart family b need not generate S. -/
theorem nativeFiniteGradedIndependentCechProductSectionMap_injective_general
    (b : ι → S) (hb : ∀ i,b i ∈ B 1) (p : ℕ) (t : Fin (p+1) → ι) :
    Function.Injective (nativeProjectiveChartDegreeZeroSectionMap B D hD (p+1)
      (∏ k : Fin (p+1),b (t k)) (nativeProjective_cechProduct_mem_degree B b hb p t)) := by
  classical
  have presentation := integerGradedFinite_exists_shiftedFree_surjection (K:=K) (S:=S) (M:=M) B D hD
  rcases presentation with ⟨s,w,he,hh⟩
  let E := integerShiftedFreePiece B w
  let hE := integerShiftedFreePiece_smul_homogeneous B w
  letI : DirectSum.Decomposition E := integerShiftedFreeDecomposition B w
  let f := integerShiftedFreeGeneratorMap (S:=S) (fun i : s => (i : M))
  let DK := nativeProjectiveKernelPiece E f
  let hK := nativeProjectiveKernelPiece_graded B E f hE
  letI : DirectSum.Decomposition DK := nativeProjectiveKernelDecomposition E D f hh
  letI : IsNoetherian S (s → S) := isNoetherian_of_isNoetherianRing_of_finite S (s → S)
  letI : IsNoetherian S f.ker := isNoetherian_of_submodule_of_noetherian S (s → S) f.ker inferInstance
  letI : Module.Finite S f.ker := inferInstance
  exact nativeProjectiveChartDegreeZeroSectionMap_injective_of_kernel B E D hE hD f hh he
    (p+1) _ _
    (nativeProjectiveChartDegreeZeroSectionMap_injective_all B E hE (p+1) (Nat.zero_lt_succ p) _ _)
    (nativeFiniteGradedIndependentCechProductSectionMap_surjective B DK hK c hc hgenC b hb p t)
/-- All original coordinate-intersection chart maps are actual bijections
for arbitrary finite graded coefficients, with no coefficient torsion-free premise. -/
theorem nativeFiniteGradedIndependentCechProductSectionMap_bijective_general
    (b : ι → S) (hb : ∀ i,b i ∈ B 1) (p : ℕ) (t : Fin (p+1) → ι) :
    Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hD (p+1)
      (∏ k : Fin (p+1),b (t k)) (nativeProjective_cechProduct_mem_degree B b hb p t)) :=
  ⟨nativeFiniteGradedIndependentCechProductSectionMap_injective_general B D hD c hc hgenC b hb p t,
    nativeFiniteGradedIndependentCechProductSectionMap_surjective B D hD c hc hgenC b hb p t⟩
end LinearStudy
