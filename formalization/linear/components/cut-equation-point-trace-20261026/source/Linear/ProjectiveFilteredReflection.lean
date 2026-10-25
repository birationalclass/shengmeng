module
public import Linear.ProjectiveFilteredPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K]

/-- A bounded-degree coordinate function has no component above that bound. -/
theorem homogeneousQuotientFiltration_component_zero
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (N m : ℕ) (hm : N < m) (a : MvPolynomial σ K ⧸ I)
    (ha : a ∈ homogeneousQuotientFiltration I N) :
    homogeneousQuotientComponent I hI m a = 0 := by
  classical
  have hle : homogeneousQuotientFiltration I N ≤
      LinearMap.ker (homogeneousQuotientComponent I hI m) := by
    unfold homogeneousQuotientFiltration
    apply Finset.sup_le
    intro k hk b hb
    change homogeneousQuotientComponent I hI m b = 0
    rw [homogeneousQuotientComponent_on_piece I hI m k b hb]
    have hmk : m ≠ k := by
      have hkN := Finset.mem_range.mp hk
      omega
    simp [hmk]
  exact hle ha

/-- An exact criterion for the ACTUAL bounded-degree coordinate filtration. -/
theorem homogeneousQuotientFiltration_mem_iff_components
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (N : ℕ) (a : MvPolynomial σ K ⧸ I) :
    a ∈ homogeneousQuotientFiltration I N ↔
      ∀ m > N, homogeneousQuotientComponent I hI m a = 0 := by
  classical
  refine ⟨fun ha m hm => homogeneousQuotientFiltration_component_zero I hI N m hm a ha, ?_⟩
  intro hzero
  obtain ⟨M, hM⟩ := homogeneousQuotientComponent_decomposition I hI a
  rw [← hM]
  apply Submodule.sum_mem
  intro m hm
  by_cases hmN : m ≤ N
  · exact Finset.le_sup (f := homogeneousQuotientPiece I)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hmN))
      (homogeneousQuotientComponent_mem_piece I hI m a)
  · rw [hzero m (Nat.lt_of_not_ge hmN)]
    exact (homogeneousQuotientFiltration I N).zero_mem

variable {n : ℕ}

/-- Injectivity and the ACTUAL homogeneous component comparison reflect the
q-scaled degree bound. This is stronger than a forward filtration inclusion. -/
theorem projectiveCoordinateDomainMap_filtration_iff
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (N : ℕ) (a : CoordinateRing n ⧸ V.ideal.toIdeal) :
    projectiveCoordinateDomainMap f V hq hf hV a ∈
        homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N) ↔
      a ∈ homogeneousQuotientFiltration V.ideal.toIdeal N := by
  refine ⟨?_, projectiveCoordinateDomainMap_filtration_mem f V hq hf hV N a⟩
  intro ha
  apply (homogeneousQuotientFiltration_mem_iff_components
    V.ideal.toIdeal V.ideal.isHomogeneous N a).mpr
  intro m hm
  apply projectiveCoordinateDomainMap_injective f V hq hf hV
  rw [map_zero, ← projectiveCoordinateDomainMap_component f V hq hf hV m a]
  exact homogeneousQuotientFiltration_component_zero V.ideal.toIdeal V.ideal.isHomogeneous
    (f.degree * N) (f.degree * m) (Nat.mul_lt_mul_of_pos_left hm hq) _ ha

theorem projectiveCoordinateDomainMap_filtration_comap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (N : ℕ) :
    (homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N)).comap
        (projectiveCoordinateDomainMap f V hq hf hV).toLinearMap =
      homogeneousQuotientFiltration V.ideal.toIdeal N := by
  ext a
  exact projectiveCoordinateDomainMap_filtration_iff f V hq hf hV N a

end LinearStudy
