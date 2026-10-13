module
public import Linear.NativeFiniteGradedCechVanishing
public import Linear.ModuleOrderedCechSectionLift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open LinearStudy AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous surjection of actual finite graded polynomial modules
induces a surjection on ACTUAL global sections of all sufficiently large
native twists. The bound is constructed from the actual graded kernel,
before all later twist degrees. It is not an assumed Serre theorem or an
assumed global lifting map. Original polynomial and ideal comparisons
and the genuine canonical identification remain separate obligations. -/
theorem coordinateNativeFiniteGraded_eventually_sections_surjective
    {E F : Type u} [AddCommGroup E] [Module K E] [Module (MvPolynomial σ K) E]
    [IsScalarTower K (MvPolynomial σ K) E]
    [AddCommGroup F] [Module K F] [Module (MvPolynomial σ K) F]
    [IsScalarTower K (MvPolynomial σ K) F]
    (D : ℤ → Submodule K E) (G : ℤ → Submodule K F)
    [DirectSum.Decomposition D] [DirectSum.Decomposition G]
    (hD : ∀ a : ℕ, ∀ d : ℤ, ∀ c : MvPolynomial σ K,
      c ∈ homogeneousSubmodule σ K a → ∀ x : E, x ∈ D d → c • x ∈ D ((a : ℤ)+d))
    (hG : ∀ a : ℕ, ∀ d : ℤ, ∀ c : MvPolynomial σ K,
      c ∈ homogeneousSubmodule σ K a → ∀ x : F, x ∈ G d → c • x ∈ G ((a : ℤ)+d))
    [Module.Finite (MvPolynomial σ K) E]
    (b : E →ₗ[MvPolynomial σ K] F)
    (hh : ∀ d : ℤ, ∀ x : E, x ∈ D d → b x ∈ G d)
    (hb : Function.Surjective b) (j : σ) :
    ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N → Function.Surjective
      ((nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        D G hD hG b hh (N : ℤ)).app ⊤) := by
  classical
  let S := MvPolynomial σ K
  let B := homogeneousSubmodule σ K
  let H := nativeProjectiveKernelPiece D b
  let hH := nativeProjectiveKernelPiece_graded B D b hD
  letI : DirectSum.Decomposition H := nativeProjectiveKernelDecomposition D G b hh
  letI : IsNoetherian S E := isNoetherian_of_isNoetherianRing_of_finite S E
  letI : IsNoetherian S b.ker :=
    isNoetherian_of_submodule_of_noetherian S E b.ker inferInstance
  letI : Module.Finite S b.ker := inferInstance
  obtain ⟨n₀,hn₀⟩ := coordinateNativeFiniteGraded_eventually_orderedCech_exactAt_succ H hH j 0
  refine ⟨n₀, fun N hN => ?_⟩
  let T := ShortComplex.mk
    (nativeProjectiveKernelSheafInclusion B D hD b N)
    (nativeProjectiveDegreeZeroSheafMap B D G hD hG b hh N)
    (nativeProjectiveKernelSheafInclusion_comp_zero B D G hD hG b hh N)
  let π := homogeneousProjπ (R := K) (σ := σ)
  let U := coordinateOpenCover (R := K) (σ := σ)
  have hcover : (⨆ i : ULift.{u} σ, Proj.basicOpen B (X i.down)) = ⊤ :=
    iSup_coordinateOpenCover_eq_top (R := K) (σ := σ)
  have hC : (T.map (Scheme.Modules.orderedBaseCechComplexFunctor π U)).ShortExact :=
    nativeProjectiveGradedKernelOrderedCech_shortExact B D G hD hG b hh
      (fun i : ULift.{u} σ => X i.down) (fun i => isHomogeneous_X K i.down)
      hcover π hb N
  exact Scheme.Modules.orderedCechShortExact_sections_surjective π U T
    (le_of_eq hcover.symm) hC (hn₀ N hN)
end MvPolynomial
