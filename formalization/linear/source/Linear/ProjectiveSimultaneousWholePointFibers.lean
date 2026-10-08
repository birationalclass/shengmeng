module
public import Linear.ProjectiveSimultaneousFiberRelations
public import Linear.ProjectiveWholeFiberGoodDimension
public import Linear.ProjectiveWholePointFiberRelation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Simultaneous original good targets with exact WHOLE PROJECTIVE fibers
and the manuscript's arbitrary nonzero representatives. The second good
open is intersected explicitly to retain the no-infinity/whole-fiber scope. -/
theorem projective_iterates_simultaneous_whole_point_fiber_relations {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (r : ℕ) (P : Polynomial ℚ), r ≤ n ∧ P ≠ 0 ∧ P.natDegree=r ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)=(r : WithBot ℕ∞) ∧
      (∃ N : ℕ, ∀ j > N, P.eval (j : ℚ)=
        (homogeneousQuotientHilbert V.ideal.toIdeal j : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i,(L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∃ d : ℕ, 0 < d ∧ (d : ℚ)=(r.factorial : ℚ)*P.leadingCoeff ∧
          ∀ k : ℕ, 0 < r → 1 < (f.iterate k).degree →
            ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧
              (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
              ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
                w 0 ≠ 0 ∧ Nat.card (projectiveLinearSection V L w)=d ∧
                ∀ z ∈ projectiveLinearSection V L w,
                  z.rep 0 ≠ 0 ∧
                  (let y := fun i : Fin n => z.rep i.succ/z.rep 0;
                   ∃ hy : normalizedProjectivePoint y ∈ V.zeroSet,
                     normalizedProjectivePoint y=z ∧
                     Nat.card ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y})=
                       (f.degree^k)^r ∧
                     (let S := (f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y};
                      ∃ hS : S.Finite,
                        letI : Fintype S := hS.fintype
                        ∀ (v : S → CoordinateVector n) (hv : ∀ x,v x ≠ 0),
                          (∀ x,Projectivization.mk ℂ (v x) (hv x)=x.val) →
                          ∃ weights : S → ℂ,(∀ x,weights x ≠ 0) ∧
                            ∀ σ : CoordinateRing n,σ.IsHomogeneous (r*((f.iterate k).degree-1)-1) →
                              ∑ x : S,weights x*MvPolynomial.eval (v x) σ=0)) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  obtain ⟨s,P,hs,hP,hdegree,hdimS,hHilbert,L,hL,hinj,hfinite,d,hd,hdHilbert,hsections⟩ :=
    projective_exists_linear_sections_in_every_affine_open V x0 hx0
  obtain ⟨r,hr,hdimR,hrank,hrelIter⟩ := projective_iterates_whole_fibers_homogeneous_relations
    f V hq hf hV hproper x0 hx0
  have hsr : s=r := by exact_mod_cast hdimS.symm.trans hdimR
  cases hsr
  obtain ⟨a,ha,hdimA,harank,hparams,hgoodIter⟩ :=
    projective_iterates_whole_good_fibers_same_dimension f V hq hf hV hproper x0 hx0
  have has : a=s := by exact_mod_cast hdimA.symm.trans hdimR
  cases has
  refine ⟨s,P,hs,hP,hdegree,hdimR,hHilbert,L,hL,hinj,hfinite,d,hd,hdHilbert,?_⟩
  intro k hrpos hqk
  obtain ⟨p1,hp1,_,hrelFib⟩ := hrelIter k
  obtain ⟨p2,hp2,_,_,hgoodFib⟩ := hgoodIter k
  have hp : p1*p2 ∉ V.affineIdeal := fun h =>
    (show V.affineIdeal.IsPrime from inferInstance).mem_or_mem h |>.elim hp1 hp2
  obtain ⟨c,hc,hex,hsect⟩ := hsections (p1*p2) hp
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hcard,hall⟩ := hsect w hw
  refine ⟨hw0,hcard,?_⟩
  intro z hz
  obtain ⟨hz0,hpval⟩ := hall z hz
  refine ⟨hz0,?_⟩
  let y := fun i : Fin n => z.rep i.succ/z.rep 0
  have hy : normalizedProjectivePoint y ∈ V.zeroSet := V.normalizedConePoint_mem z.rep hz.1 hz0
  have hyz : normalizedProjectivePoint y=z :=
    (normalizedProjectivePoint_coordinate_ratios z.rep (Projectivization.rep_nonzero z) hz0).trans
      (Projectivization.mk_rep z)
  have hpvals : MvPolynomial.eval y p1 ≠ 0 ∧ MvPolynomial.eval y p2 ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [MvPolynomial.eval_mul] using hpval)
  obtain ⟨hgeom,hrel⟩ := hrelFib y hy hpvals.1 hrpos hqk
  obtain ⟨hSf,hchart,hfiniteQ,hred,hScard⟩ := hgoodFib y hy hpvals.2
  exact ⟨hy,hyz,hScard,projective_whole_point_fiber_arbitrary_representative_relation
    (f.iterate k) V y hy (f.iterate_total_invariance V.zeroSet hV k) hchart hrel⟩

end LinearStudy
