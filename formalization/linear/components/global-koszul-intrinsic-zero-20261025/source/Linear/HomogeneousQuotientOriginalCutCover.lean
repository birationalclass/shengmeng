module
public import Linear.HomogeneousCutChartCoverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- Original point avoidance gives a cover of the WHOLE ORIGINAL
ambient Proj by its original a-chart and original equation-nonvanishing
opens. Nullstellensatz applies to the actual ideal,retaining nilpotents
and ALL nonclosed native primes. No desired scheme coverage is assumed. -/
theorem homogeneousQuotient_chart_or_original_equation
    (I : Ideal (CoordinateRing n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℂ))
    (F : Fin r → CoordinateRing n) (a : CoordinateRing n)
    (havoid : ∀ v : CoordinateVector n,
      v ∈ MvPolynomial.zeroLocus ℂ (I ⊔ Ideal.span (Set.range F)) →
        MvPolynomial.eval v a = 0 → v = 0) :
    letI := homogeneousQuotientGrading I hI
    ∀ p : Proj (homogeneousQuotientPiece I),
      p ∈ Proj.basicOpen (homogeneousQuotientPiece I) (Ideal.Quotient.mk I a) ∨
        ∃ i : Fin r,p ∈ Proj.basicOpen (homogeneousQuotientPiece I) (Ideal.Quotient.mk I (F i)) := by
  letI := homogeneousQuotientGrading I hI
  intro p
  by_cases hpa : p ∈ Proj.basicOpen (homogeneousQuotientPiece I) (Ideal.Quotient.mk I a)
  · exact Or.inl hpa
  right
  by_contra hn
  have hpa' : Ideal.Quotient.mk I a ∈ p.asHomogeneousIdeal.toIdeal := by
    exact not_not.mp hpa
  have hFp (i : Fin r) : Ideal.Quotient.mk I (F i) ∈ p.asHomogeneousIdeal.toIdeal := by
    by_contra hi
    exact hn ⟨i,hi⟩
  apply p.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le (homogeneousQuotientPiece I)).mpr
  intro m hm z hz
  obtain ⟨G,hG,rfl⟩ := (homogeneousQuotientPiece_mem_iff I m z).mp hz
  let P := p.asHomogeneousIdeal.toIdeal.comap (Ideal.Quotient.mk I)
  let J : Ideal (CoordinateRing n) := (I ⊔ Ideal.span (Set.range F)) ⊔ Ideal.span {a}
  letI : P.IsPrime := Ideal.comap_isPrime (Ideal.Quotient.mk I) _
  have hJ : J ≤ P := by
    apply sup_le
    · apply sup_le
      · intro G hG
        change Ideal.Quotient.mk I G ∈ p.asHomogeneousIdeal.toIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hG]
        exact Ideal.zero_mem _
      · apply Ideal.span_le.mpr
        rintro _ ⟨i,rfl⟩
        exact hFp i
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      exact hpa'
  have hG0 : MvPolynomial.eval (0 : CoordinateVector n) G = 0 := by
    have he := homogeneous_eval_smul hG (0 : ℂ) (0 : CoordinateVector n)
    simpa [zero_pow (Nat.ne_of_gt hm)] using he
  have hGrad : G ∈ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) J]
    intro v hv
    have hvI : v ∈ MvPolynomial.zeroLocus ℂ (I ⊔ Ideal.span (Set.range F)) :=
      fun G hG => hv G (Ideal.mem_sup_left hG)
    have hva : MvPolynomial.eval v a = 0 :=
      hv a (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
    rw [havoid v hvI hva]
    exact hG0
  exact (show P.IsPrime from inferInstance).radical_le_iff.mpr hJ hGrad

end LinearStudy