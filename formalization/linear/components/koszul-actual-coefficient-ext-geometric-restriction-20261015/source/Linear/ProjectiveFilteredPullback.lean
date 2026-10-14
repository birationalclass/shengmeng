module
public import Linear.HomogeneousCoordinateFiltration
public import Linear.ProjectiveGradedPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K]

/-- Multiplication respects the ACTUAL total-degree coordinate filtration. -/
theorem homogeneousQuotientFiltration_mul_mem (I : Ideal (MvPolynomial σ K))
    (N M : ℕ) (a b : MvPolynomial σ K ⧸ I)
    (ha : a ∈ homogeneousQuotientFiltration I N)
    (hb : b ∈ homogeneousQuotientFiltration I M) :
    a * b ∈ homogeneousQuotientFiltration I (N + M) := by
  obtain ⟨H, hH, rfl⟩ := (homogeneousQuotientFiltration_mem_iff I N a).mp ha
  obtain ⟨G, hG, rfl⟩ := (homogeneousQuotientFiltration_mem_iff I M b).mp hb
  exact (homogeneousQuotientFiltration_mem_iff I (N + M) _).mpr
    ⟨H * G, (MvPolynomial.totalDegree_mul H G).trans (Nat.add_le_add hH hG), by simp⟩

variable {n : ℕ}

/-- The ORIGINAL pullback scales the actual bounded-degree filtration by q. -/
theorem projectiveCoordinateDomainMap_filtration_mem
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (N : ℕ) (a : CoordinateRing n ⧸ V.ideal.toIdeal)
    (ha : a ∈ homogeneousQuotientFiltration V.ideal.toIdeal N) :
    projectiveCoordinateDomainMap f V hq hf hV a ∈
      homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N) := by
  classical
  have hle : homogeneousQuotientFiltration V.ideal.toIdeal N ≤
      (homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N)).comap
        (projectiveCoordinateDomainMap f V hq hf hV).toLinearMap := by
    unfold homogeneousQuotientFiltration
    apply Finset.sup_le
    intro m hm x hx
    have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    apply Finset.le_sup (f := homogeneousQuotientPiece V.ideal.toIdeal)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.mul_le_mul_left f.degree hmN)))
    exact projectiveCoordinateDomainMap_piece_mem f V hq hf hV m x hx
  exact hle ha

def projectiveCoordinateFilteredPullback
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (N : ℕ) :
    homogeneousQuotientFiltration V.ideal.toIdeal N →ₗ[ℂ]
      homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N) :=
  ((projectiveCoordinateDomainMap f V hq hf hV).toLinearMap.domRestrict
    (homogeneousQuotientFiltration V.ideal.toIdeal N)).codRestrict
      (homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N))
      (fun a => projectiveCoordinateDomainMap_filtration_mem f V hq hf hV N a a.property)

theorem projectiveCoordinateFilteredPullback_injective
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (N : ℕ) :
    Function.Injective (projectiveCoordinateFilteredPullback f V hq hf hV N) := by
  intro a b hab
  apply Subtype.ext
  apply projectiveCoordinateDomainMap_injective f V hq hf hV
  exact congrArg Subtype.val hab

/-- A genuine dimension inequality for actual bounded-degree function spaces.
The stronger generic-rank growth comparison still needs proof. -/
theorem projectiveCoordinateFiltration_pullback_le
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (N : ℕ) :
    Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) ≤
      Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N)) := by
  letI := homogeneousQuotientFiltration_finite V.ideal.toIdeal (f.degree * N)
  exact LinearMap.finrank_le_finrank_of_injective
    (projectiveCoordinateFilteredPullback_injective f V hq hf hV N)

end LinearStudy
