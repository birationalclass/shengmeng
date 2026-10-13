module
public import Linear.NativeShiftedFreeCechVanishing
public import Linear.NativeProjectiveGradedKernelCech
public import Linear.IntegerGradedFiniteFreeSurjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open LinearStudy AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/- The dimension-shift argument is the reviewed proof pattern from
CBirkbeck/AINTLIB ab1451487da02cd4483d0e2cdb2cc9e44bbbac17,
EllipticCurve/ProjectiveSpacePositiveTwistCechVanishing.lean.
Here the source is the CONSTRUCTED actual homogeneous shifted-free
surjection, and every twist and kernel is our native fraction sheaf.
No pole sheaf, foreign equivalence or eventual-vanishing input is used. -/

private theorem coordinateNativeFiniteGraded_eventually_of_card_le_add
    (j : σ) (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
      [IsScalarTower K (MvPolynomial σ K) M]
      (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
      (hD : ∀ a : ℕ, ∀ d : ℤ, ∀ c : MvPolynomial σ K,
        c ∈ homogeneousSubmodule σ K a → ∀ x : M, x ∈ D d →
          c • x ∈ D ((a : ℤ)+d)) [Module.Finite (MvPolynomial σ K) M]
      (q : ℕ) (hcard : Fintype.card (ULift.{u} σ) ≤ (q+1)+n),
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N →
      (Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := K) (σ := σ))
        (nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD N)
        (coordinateOpenCover (R := K) (σ := σ))).ExactAt (q+1) := by
  induction n with
  | zero =>
      intro M _ _ _ _ D _ hD _ q hcard
      refine ⟨0, fun N _ => ?_⟩
      apply Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le
      simpa using hcard
  | succ n ih =>
      intro M _ _ _ _ D _ hD _ q hcard
      classical
      by_cases hq : Fintype.card (ULift.{u} σ) ≤ q+1
      · refine ⟨0, fun N _ => ?_⟩
        exact Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le _ _ _ _ hq
      · obtain ⟨s, w, hb, hh⟩ :=
          integerGradedFinite_exists_shiftedFree_surjection (homogeneousSubmodule σ K) D hD
        let B := homogeneousSubmodule σ K
        let E := integerShiftedFreePiece B w
        let hE := integerShiftedFreePiece_smul_homogeneous B w
        let b := integerShiftedFreeGeneratorMap (S := MvPolynomial σ K) (fun i : s => (i : M))
        letI : DirectSum.Decomposition E := integerShiftedFreeDecomposition B w
        let Dker := nativeProjectiveKernelPiece E b
        let hK := nativeProjectiveKernelPiece_graded B E b hE
        letI : DirectSum.Decomposition Dker := nativeProjectiveKernelDecomposition E D b hh
        letI : IsNoetherian (MvPolynomial σ K) (s → MvPolynomial σ K) :=
          isNoetherian_of_isNoetherianRing_of_finite (MvPolynomial σ K) _
        letI : IsNoetherian (MvPolynomial σ K) b.ker :=
          isNoetherian_of_submodule_of_noetherian (MvPolynomial σ K) _ b.ker inferInstance
        letI : Module.Finite (MvPolynomial σ K) b.ker := inferInstance
        have hcard' : Fintype.card (ULift.{u} σ) ≤ ((q+1)+1)+n := by omega
        obtain ⟨bK, hbK⟩ := ih b.ker Dker hK (q+1) hcard'
        obtain ⟨bE, hbE⟩ := coordinateNativeShiftedFree_eventually_orderedCech_exactAt_succ
          (K := K) j w
        refine ⟨max bE bK, fun N hN => ?_⟩
        have hNE : bE ≤ N := le_trans (le_max_left _ _) hN
        have hNK : bK ≤ N := le_trans (le_max_right _ _) hN
        have hFree := hbE N hNE q
        have hKer := hbK N hNK
        let T := ShortComplex.mk
          (nativeProjectiveKernelSheafInclusion B E hE b N)
          (nativeProjectiveDegreeZeroSheafMap B E D hE hD b hh N)
          (nativeProjectiveKernelSheafInclusion_comp_zero B E D hE hD b hh N)
        let F := Scheme.Modules.orderedBaseCechComplexFunctor
          (homogeneousProjπ (R := K) (σ := σ))
          (coordinateOpenCover (R := K) (σ := σ))
        have ha : ∀ i : ULift.{u} σ, X i.down ∈ B 1 :=
          fun i => isHomogeneous_X K i.down
        have hcover : (⨆ i : ULift.{u} σ, Proj.basicOpen B (X i.down)) = ⊤ :=
          iSup_coordinateOpenCover_eq_top (R := K) (σ := σ)
        have hC : (T.map F).ShortExact :=
          nativeProjectiveGradedKernelOrderedCech_shortExact B E D hE hD b hh
            (fun i : ULift.{u} σ => X i.down) ha hcover
            (homogeneousProjπ (R := K) (σ := σ)) hb N
        rw [HomologicalComplex.exactAt_iff_isZero_homology] at hFree hKer ⊢
        exact (hC.homology_exact₃ (q+1) ((q+1)+1)
          (by simp [ComplexShape.up_Rel])).isZero_X₂
          (hFree.eq_of_src _ _) (hKer.eq_of_tgt _ _)

/-- A finite actual integer-graded polynomial module has an eventual bound
for exactness of its actual native-twist ordered coordinate Cech complex
at each fixed positive degree. The bound is chosen before every later twist.
This is Cech exactness, not yet derived sheaf cohomology or original4.2. -/
theorem coordinateNativeFiniteGraded_eventually_orderedCech_exactAt_succ
    {M : Type u} [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
    [IsScalarTower K (MvPolynomial σ K) M]
    (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
    (hD : ∀ a : ℕ, ∀ d : ℤ, ∀ c : MvPolynomial σ K,
      c ∈ homogeneousSubmodule σ K a → ∀ x : M, x ∈ D d → c • x ∈ D ((a : ℤ)+d))
    [Module.Finite (MvPolynomial σ K) M] (j : σ) (q : ℕ) :
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N →
      (Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := K) (σ := σ))
        (nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD N)
        (coordinateOpenCover (R := K) (σ := σ))).ExactAt (q+1) :=
  coordinateNativeFiniteGraded_eventually_of_card_le_add j
    (Fintype.card (ULift.{u} σ)) M D hD q (by omega)

/-- There is ONE constructed bound for all later integer twists and all
positive ordered-Cech degrees of the actual native finite-graded sheaf. -/
theorem coordinateNativeFiniteGraded_eventually_allPositive_orderedCech_exactAt
    {M : Type u} [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
    [IsScalarTower K (MvPolynomial σ K) M]
    (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
    (hD : ∀ a : ℕ, ∀ d : ℤ, ∀ c : MvPolynomial σ K,
      c ∈ homogeneousSubmodule σ K a → ∀ x : M, x ∈ D d → c • x ∈ D ((a : ℤ)+d))
    [Module.Finite (MvPolynomial σ K) M] (j : σ) :
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N → ∀ q : ℕ,
      (Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := K) (σ := σ))
        (nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD N)
        (coordinateOpenCover (R := K) (σ := σ))).ExactAt (q+1) := by
  classical
  choose b hb using fun q =>
    coordinateNativeFiniteGraded_eventually_orderedCech_exactAt_succ D hD j q
  refine ⟨(Finset.range (Fintype.card (ULift.{u} σ))).sup b, fun N hN q => ?_⟩
  by_cases hq : Fintype.card (ULift.{u} σ) ≤ q+1
  · exact Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le _ _ _ _ hq
  · have hmem : q ∈ Finset.range (Fintype.card (ULift.{u} σ)) := by
      rw [Finset.mem_range]
      omega
    exact hb q N (le_trans (Finset.le_sup hmem) hN)

end MvPolynomial
