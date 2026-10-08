module
/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

Adapted proof route from mathlib PR 9819, commit
413e5b872a7c758e0eb91f99cb96d6a61c81f0a2.
Specialize to a fixed base field and degree-one generators. Actual submodules,
quotients and rank-nullity replace changing degree-zero rings and category transport.
-/
public import Linear.GradedScalarInductionModules
public import Linear.GradedHilbertSeriesRecurrence
public import Linear.HomogeneousAdjoinGenerators
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
universe uK uA uM
variable {K : Type uK} [Field K]

private theorem gradedHilbertSerre_induction (N : ℕ) :
    ∀ (A : Type uA) [CommRing A] [Algebra K A] [IsNoetherianRing A]
      (M : Type uM) [AddCommGroup M] [Module K M] [Module A M]
      [IsScalarTower K A M] [Module.Finite A M]
      (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
      (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul 𝒜 ℳ] [∀ n, Module.Finite K (ℳ n)]
      (s : Finset A), s.card = N → Algebra.adjoin K (s : Set A) = ⊤ →
      (∀ x ∈ s, x ∈ 𝒜 1) →
      ∃ p : Polynomial ℤ, (1 - PowerSeries.X) ^ N * gradedHilbertSeries ℳ = (p : PowerSeries ℤ) := by
  classical
  induction N with
  | zero =>
      intro A instA instKA instNA M instM instKM instAM instTower instFM
        𝒜 instGrA ℳ instGrM instGSm instFp s hcard hgen hdegree
      have hs : s = ∅ := Finset.card_eq_zero.mp hcard
      subst s
      obtain ⟨p, hp⟩ := gradedHilbertSeries_polynomial_of_empty_generators ℳ
        (by simpa only [Finset.coe_empty] using hgen)
      exact ⟨p, by simpa using hp.symm⟩
  | succ N ih =>
      intro A instA instKA instNA M instM instKM instAM instTower instFM
        𝒜 instGrA ℳ instGrM instGSm instFp s hcard hgen hdegree
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      have hx₁ : x ∈ 𝒜 1 := hdegree x hx
      let s' := s.erase x
      have hs' : s'.card = N := by simp only [s', Finset.card_erase_of_mem hx]; omega
      have hgen' : Algebra.adjoin K (insert x (s' : Set A)) = ⊤ := by
        simpa only [s', ← Finset.coe_insert, Finset.insert_erase hx] using hgen
      let B := Algebra.adjoin K (s' : Set A)
      let 𝒜' := gradedSubalgebraPiece 𝒜 B
      letI : GradedAlgebra 𝒜' := gradedSubalgebraGrading 𝒜 B
        (homogeneousAdjoin 𝒜 (s' : Set A)
          (fun a ha => ⟨1, hdegree a (Finset.mem_of_mem_erase ha)⟩))
      letI : IsNoetherianRing B := finiteAdjoin_isNoetherian s'
      let sB := adjoinLiftedGenerators (K := K) s'
      have hsB : sB.card = N := (adjoinLiftedGenerators_card s').trans hs'
      have hgenB : Algebra.adjoin K (sB : Set B) = ⊤ := adjoinLiftedGenerators_generate s'
      have hdegreeB : ∀ a ∈ sB, a ∈ 𝒜' 1 :=
        adjoinLiftedGenerators_homogeneous 𝒜 s' 1
          (fun a ha => hdegree a (Finset.mem_of_mem_erase ha))

      let P := (gradedScalarKernel 𝒜 ℳ 1 x hx₁).toSubmodule
      let PK := P.restrictScalars K
      let ℳK := gradedSubmodulePiece ℳ PK
      letI : Module.Finite B PK := gradedScalarKernel_finite_over_adjoin 𝒜 ℳ 1 x hx₁
        (s' : Set A) hgen'
      letI : DirectSum.Decomposition ℳK := gradedSubmoduleDecomposition ℳ PK
        (gradedScalarKernel 𝒜 ℳ 1 x hx₁).is_homogeneous'
      letI : SetLike.GradedSMul 𝒜 ℳK := gradedScalarKernelGradedSMul 𝒜 ℳ 1 x hx₁
      letI : SetLike.GradedSMul 𝒜' ℳK := gradedSubalgebraModuleGradedSMul 𝒜 ℳK B
      letI : ∀ n, Module.Finite K (ℳK n) := fun n => gradedSubmodulePiece_finite ℳ PK n
      obtain ⟨pK, hpK⟩ := ih B PK 𝒜' ℳK sB hsB hgenB hdegreeB

      let Q := (gradedScalarImage 𝒜 ℳ 1 x hx₁).toSubmodule
      let QK := Q.restrictScalars K
      let MC := M ⧸ QK
      let ℳC := gradedQuotientPiece ℳ QK
      letI : Module A MC := gradedScalarCokernelModule 𝒜 ℳ 1 x hx₁
      letI : IsScalarTower K A MC := inferInstanceAs (IsScalarTower K A (M ⧸ Q))
      letI : Module.Finite B MC := gradedScalarCokernel_finite_over_adjoin 𝒜 ℳ 1 x hx₁
        (s' : Set A) hgen'
      letI : DirectSum.Decomposition ℳC := gradedQuotientDecomposition ℳ QK
        (gradedScalarImage 𝒜 ℳ 1 x hx₁).is_homogeneous'
      letI : SetLike.GradedSMul 𝒜 ℳC := gradedScalarCokernelGradedSMul 𝒜 ℳ 1 x hx₁
      letI : SetLike.GradedSMul 𝒜' ℳC := gradedSubalgebraModuleGradedSMul 𝒜 ℳC B
      letI : ∀ n, Module.Finite K (ℳC n) := fun n => gradedQuotientPiece_finite ℳ QK n
      obtain ⟨pC, hpC⟩ := ih B MC 𝒜' ℳC sB hsB hgenB hdegreeB

      have hrec := gradedHilbertSeries_scalar_recurrence 𝒜 ℳ 1 x hx₁
      simp only [pow_one] at hrec
      change (1 - PowerSeries.X) * gradedHilbertSeries ℳ =
        gradedHilbertSeries ℳC - PowerSeries.X * gradedHilbertSeries ℳK at hrec
      refine ⟨pC - Polynomial.X * pK, ?_⟩
      calc
        (1 - PowerSeries.X) ^ (N + 1) * gradedHilbertSeries ℳ =
            (1 - PowerSeries.X) ^ N * ((1 - PowerSeries.X) * gradedHilbertSeries ℳ) := by ring
        _ = (1 - PowerSeries.X) ^ N *
            (gradedHilbertSeries ℳC - PowerSeries.X * gradedHilbertSeries ℳK) := by rw [hrec]
        _ = (1 - PowerSeries.X) ^ N * gradedHilbertSeries ℳC -
            PowerSeries.X * ((1 - PowerSeries.X) ^ N * gradedHilbertSeries ℳK) := by ring
        _ = (pC : PowerSeries ℤ) - PowerSeries.X * (pK : PowerSeries ℤ) := by rw [hpC, hpK]
        _ = ((pC - Polynomial.X * pK : Polynomial ℤ) : PowerSeries ℤ) := by simp

/-- Hilbert--Serre for an actual finite graded module with degree-one algebra generators.
The polynomial denominator and numerator are proved; neither is supplied. -/
theorem gradedHilbertSeries_rational
    {A : Type uA} [CommRing A] [Algebra K A] [IsNoetherianRing A]
    {M : Type uM} [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [Module.Finite A M]
    (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
    (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] [∀ n, Module.Finite K (ℳ n)]
    (s : Finset A) (hgen : Algebra.adjoin K (s : Set A) = ⊤)
    (hdegree : ∀ x ∈ s, x ∈ 𝒜 1) :
    ∃ p : Polynomial ℤ,
      (1 - PowerSeries.X) ^ s.card * gradedHilbertSeries ℳ = (p : PowerSeries ℤ) :=
  gradedHilbertSerre_induction s.card A M 𝒜 ℳ s rfl hgen hdegree

end LinearStudy
