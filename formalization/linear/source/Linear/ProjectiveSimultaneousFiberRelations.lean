module
public import Linear.ProjectiveLinearSectionGoodTargets
public import Linear.ProjectiveWholeFiberHomogeneousRelation
public import Linear.ProjectiveFiberRepresentativeRelation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every original iterate admits d=deg V simultaneous GOOD targets on ONE
actual linear section. The same actual r is the original chart dimension.
For EVERY selected target, the whole original in-V fiber, its q^r point
count, common ambient geometry and homogeneous relation are derived.
Global scheme/Koszul/transversality comparisons are not asserted here. -/
theorem projective_iterates_simultaneous_linear_section_fiber_relations {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (r : ℕ) (P : Polynomial ℚ), r ≤ n ∧ P ≠ 0 ∧ P.natDegree = r ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      (∃ N : ℕ, ∀ j > N, P.eval (j : ℚ) =
        (homogeneousQuotientHilbert V.ideal.toIdeal j : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∃ d : ℕ, 0 < d ∧ (d : ℚ) = (r.factorial : ℚ)*P.leadingCoeff ∧
          ∀ k : ℕ, 0 < r → 1 < (f.iterate k).degree →
            ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧
              (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
              ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
                w 0 ≠ 0 ∧ Nat.card (projectiveLinearSection V L w) = d ∧
                ∀ z ∈ projectiveLinearSection V L w,
                  z.rep 0 ≠ 0 ∧
                  (let y := fun i : Fin n => z.rep i.succ/z.rep 0;
                   ∃ hy : normalizedProjectivePoint y ∈ V.zeroSet,
                     normalizedProjectivePoint y = z ∧
                     ProjectiveWholeAmbientFiberConclusion (f.iterate k) V y hy r ∧
                     ProjectiveWholeFiberHomogeneousRelationConclusion (f.iterate k) V y r) := by
  obtain ⟨s,P,hs,hP,hdegree,hdimS,hHilbert,L,hL,hinj,hfinite,d,hd,hdHilbert,hsections⟩ :=
    projective_exists_linear_sections_in_every_affine_open V x0 hx0
  obtain ⟨r,hr,hdimR,hrank,hiter⟩ := projective_iterates_whole_fibers_homogeneous_relations
    f V hq hf hV hproper x0 hx0
  have hsr : s=r := by exact_mod_cast hdimS.symm.trans hdimR
  cases hsr
  refine ⟨s,P,hs,hP,hdegree,hdimR,hHilbert,L,hL,hinj,hfinite,d,hd,hdHilbert,?_⟩
  intro k hrpos hqk
  obtain ⟨p,hp,hnonempty,hfibers⟩ := hiter k
  obtain ⟨c,hc,hex,hsect⟩ := hsections p hp
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hcard,hgood⟩ := hsect w hw
  refine ⟨hw0,hcard,?_⟩
  intro z hz
  obtain ⟨hz0,hzp⟩ := hgood z hz
  refine ⟨hz0,?_⟩
  let y := fun i : Fin n => z.rep i.succ/z.rep 0
  have hy : normalizedProjectivePoint y ∈ V.zeroSet := V.normalizedConePoint_mem z.rep hz.1 hz0
  have hyz : normalizedProjectivePoint y = z :=
    (normalizedProjectivePoint_coordinate_ratios z.rep (Projectivization.rep_nonzero z) hz0).trans
      (Projectivization.mk_rep z)
  exact ⟨hy,hyz,hfibers y hy hzp hrpos hqk⟩

end LinearStudy
