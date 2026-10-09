module
public import Linear.ProjectiveActualFamilyRelation
public import Linear.ProjectivePulledSectionGlobalReduced
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory

/-- The same original f,V, the same finite linear normalization, and the
same parameter give both the actual whole-fiber supported relation and
the entire native finite reduced pulled-cut scheme. The two good opens
are intersected; no independently chosen point family is substituted.
This is the entrance data for geometric lifting, not the lifting itself. -/
theorem projective_iterates_actual_family_native_finite_reduced_cut {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (r : ℕ) (P : Polynomial ℚ),r ≤ n ∧ P ≠ 0 ∧ P.natDegree=r ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)=(r : WithBot ℕ∞) ∧
      (∃ N : ℕ,∀ j > N,P.eval (j : ℚ)=
        (homogeneousQuotientHilbert V.ideal.toIdeal j : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        ∃ hL : ∀ i,(L i).IsHomogeneous 1,
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∃ d : ℕ,0 < d ∧ (d : ℚ)=(r.factorial : ℚ)*P.leadingCoeff ∧
          ∀ k : ℕ,0 < r → 1 < (f.iterate k).degree →
            ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
              (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
              ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
                ProjectiveActualFamilyRelationConclusion (f.iterate k) V L w d ∧
                (let C := MvPolynomial (Fin n) ℂ ⧸
                  (projectivePulledLinearSectionIdeal (f.iterate k) V L w).map
                    (affineChartPolynomialMap (K := ℂ)).toRingHom;
                 w 0 ≠ 0 ∧ _root_.IsReduced C ∧ Module.Finite ℂ C ∧
                   Nonempty (projectivePulledLinearSectionScheme (f.iterate k) V L hL w ≅
                     Spec (CommRingCat.of C)) ∧
                   AlgebraicGeometry.IsReduced
                     (projectivePulledLinearSectionScheme (f.iterate k) V L hL w)) := by
  obtain ⟨r,P,hr,hP,hdeg,hdim,hHilbert,L,hL,hinj,hfinite,d,hd,hdHilbert,hrelations⟩ :=
    projective_iterates_actual_family_supported_relation f V hq hf hV hproper x0 hx0
  refine ⟨r,P,hr,hP,hdeg,hdim,hHilbert,L,hL,hinj,hfinite,d,hd,hdHilbert,?_⟩
  intro k hrpos hqk
  obtain ⟨c₁,hc₁,_,hrel⟩ := hrelations k hrpos hqk
  obtain ⟨c₂,hc₂,_,hcut⟩ := projectivePulledLinearSection_exists_global_finite_reduced_schemes
    (f.iterate k) V (f.iterate_degree_pos hq k) (f.iterate_surjective hf k)
    (f.iterate_total_invariance V.zeroSet hV k) L hL hinj hfinite x0 hx0
  have hc : c₁*c₂ ≠ 0 := mul_ne_zero hc₁ hc₂
  have hex : ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w (c₁*c₂) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (MvPolynomial.funext (fun w => by simpa using h w))
  refine ⟨c₁*c₂,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw₁,hw₂⟩ := mul_ne_zero_iff.mp (by simpa only [MvPolynomial.eval_mul] using hw)
  exact ⟨hrel w hw₁,hcut w hw₂⟩

end LinearStudy
