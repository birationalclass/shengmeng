module
public import Linear.HomogeneousCoordinateGrading
public import Linear.ProjectiveChart
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory
variable {n : ℕ}

/-- Point avoidance of a hypersurface gives WHOLE native Proj coverage
for the ACTUAL homogeneous quotient, including nonclosed primes and
nilpotents. Nullstellensatz is applied to the original polynomial ideal. -/
theorem homogeneousCut_basicOpen_eq_top_of_point_avoidance
    (I : Ideal (CoordinateRing n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℂ))
    (H : CoordinateRing n)
    (havoid : ∀ v : CoordinateVector n, v ∈ MvPolynomial.zeroLocus ℂ I →
      MvPolynomial.eval v H=0 → v=0) :
    letI := homogeneousQuotientGrading I hI
    Proj.basicOpen (homogeneousQuotientPiece I) (Ideal.Quotient.mk I H)=⊤ := by
  letI := homogeneousQuotientGrading I hI
  apply top_le_iff.mp
  intro p _
  change Ideal.Quotient.mk I H ∉ p.asHomogeneousIdeal
  intro hpH
  apply p.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le (homogeneousQuotientPiece I)).mpr
  intro m hm a ha
  obtain ⟨G,hG,rfl⟩ := (homogeneousQuotientPiece_mem_iff I m a).mp ha
  let P := p.asHomogeneousIdeal.toIdeal.comap (Ideal.Quotient.mk I)
  let J : Ideal (CoordinateRing n) := I ⊔ Ideal.span {H}
  letI : P.IsPrime := Ideal.comap_isPrime (Ideal.Quotient.mk I) _
  have hJ : J ≤ P := by
    apply sup_le
    · intro F hF
      change Ideal.Quotient.mk I F ∈ p.asHomogeneousIdeal.toIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF]
      exact Ideal.zero_mem _
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      exact hpH
  have hG0 : MvPolynomial.eval (0 : CoordinateVector n) G=0 := by
    have he := homogeneous_eval_smul hG (0 : ℂ) (0 : CoordinateVector n)
    simpa [zero_pow (Nat.ne_of_gt hm)] using he
  have hGrad : G ∈ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) J]
    intro v hv
    have hvI : v ∈ MvPolynomial.zeroLocus ℂ I :=
      fun F hF => hv F (Ideal.mem_sup_left hF)
    have hvH : MvPolynomial.eval v H=0 := hv H (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
    rw [havoid v hvI hvH]
    exact hG0
  exact (show P.IsPrime from inferInstance).radical_le_iff.mpr hJ hGrad

/-- If the actual homogeneous cut has no point on H=0, its ENTIRE Proj
is its native affine H-chart. This is a scheme isomorphism, not merely
a bijection of complex points. -/
theorem homogeneousCut_exists_native_chart_scheme_iso
    (I : Ideal (CoordinateRing n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℂ))
    (H : CoordinateRing n) (m : ℕ) (hH : H.IsHomogeneous m) (hm : 0 < m)
    (havoid : ∀ v : CoordinateVector n, v ∈ MvPolynomial.zeroLocus ℂ I →
      MvPolynomial.eval v H=0 → v=0) :
    letI := homogeneousQuotientGrading I hI
    Nonempty (Proj (homogeneousQuotientPiece I) ≅
      Spec (CommRingCat.of (HomogeneousLocalization.Away
        (homogeneousQuotientPiece I) (Ideal.Quotient.mk I H)))) := by
  letI := homogeneousQuotientGrading I hI
  let X := Proj (homogeneousQuotientPiece I)
  have htop := homogeneousCut_basicOpen_eq_top_of_point_avoidance I hI H havoid
  have hg : Ideal.Quotient.mk I H ∈ homogeneousQuotientPiece I m := ⟨H,hH,rfl⟩
  exact ⟨(Scheme.topIso X).symm.trans
    ((Scheme.isoOfEq X htop.symm).trans (Proj.basicOpenIsoSpec _ _ hg hm))⟩

end LinearStudy
