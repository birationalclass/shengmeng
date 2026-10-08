module
public import Linear.ProjectiveFiberFamily
public import Linear.ProjectiveSupportedEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual point-set data and nonzero supported evaluation functional
needed before the geometric lifting. No Koszul/cohomology or scheme
intersection conclusion is put in an assumption or this definition. -/
def ProjectiveActualFamilyRelationConclusion {n r : ℕ}
    (F : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) (d : ℕ) : Prop :=
  ∃ hd : 0 < d, ∃ y : Fin d → ProjectivePoint n,
    Function.Injective y ∧ Set.range y=projectiveLinearSection V L w ∧
    (∀ i, (F.onPoints ⁻¹' {y i}).Finite ∧
      Nat.card (F.onPoints ⁻¹' {y i})=F.degree^r) ∧
    (∀ i j,i ≠ j → Disjoint (F.onPoints ⁻¹' {y i}) (F.onPoints ⁻¹' {y j})) ∧
    (let S := F.onPoints ⁻¹' projectiveLinearSection V L w;
     (⋃ i,F.onPoints ⁻¹' {y i})=S ∧ S ⊆ V.zeroSet ∧
     {x : ProjectivePoint n | x ∈ V.zeroSet ∧ ∀ i,
       MvPolynomial.eval x.rep
         (MvPolynomial.aeval F.forms (projectiveLinearSectionForms L w i))=0}=S ∧
     ∃ hS : S.Finite,Nat.card S=d*F.degree^r ∧
       letI : Fintype S := hS.fintype
       ∀ (v : S → CoordinateVector n) (hv : ∀ x,v x ≠ 0),
         (∀ x,Projectivization.mk ℂ (v x) (hv x)=x.val) →
         ∃ weights : S → ℂ,weights ≠ 0 ∧
           (∀ x : S,F.onPoints x.val ≠ y ⟨0,hd⟩ → weights x=0) ∧
           (∀ x : S,F.onPoints x.val=y ⟨0,hd⟩ → weights x ≠ 0) ∧
           weightedEvaluation weights ≠ 0 ∧
           ∀ P : MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ (r*(F.degree-1)-1),
             weightedEvaluation weights
               (homogeneousPointEvaluation (r*(F.degree-1)-1) v P)=0)

/-- From the SAME original f,V, every iterate yields the enumerated d
actual targets, disjoint whole fibers, exact total size, actual pullback
common POINTS, and nonzero functional supported on the first fiber.
This closes the finite-point entrance to Section 4, not its geometric
Koszul/proper-duality/Serre lifting or scheme intersection. -/
theorem projective_iterates_actual_family_supported_relation {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (r : ℕ) (P : Polynomial ℚ),r ≤ n ∧ P ≠ 0 ∧ P.natDegree=r ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)=(r : WithBot ℕ∞) ∧
      (∃ N : ℕ,∀ j > N,P.eval (j : ℚ)=
        (homogeneousQuotientHilbert V.ideal.toIdeal j : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i,(L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∃ d : ℕ,0 < d ∧ (d : ℚ)=(r.factorial : ℚ)*P.leadingCoeff ∧
          ∀ k : ℕ,0 < r → 1 < (f.iterate k).degree →
            ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
              (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
              ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
                ProjectiveActualFamilyRelationConclusion (f.iterate k) V L w d := by
  classical
  obtain ⟨r,P,hr,hP,hdegree,hdim,hHilbert,L,hL,hinj,hfinite,d,hd,hdHilbert,hsections⟩ :=
    projective_iterates_simultaneous_whole_point_fiber_relations f V hq hf hV hproper x0 hx0
  refine ⟨r,P,hr,hP,hdegree,hdim,hHilbert,L,hL,hinj,hfinite,d,hd,hdHilbert,?_⟩
  intro k hrpos hqk
  obtain ⟨c,hc,hex,hsect⟩ := hsections k hrpos hqk
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hZcard,hpoints⟩ := hsect w hw
  let F := f.iterate k
  let Z := projectiveLinearSection V L w
  have hfib : ∀ z ∈ Z,(F.onPoints ⁻¹' {z}).Finite ∧
      Nat.card (F.onPoints ⁻¹' {z})=F.degree^r := by
    intro z hz
    obtain ⟨hz0,hy,hyz,hcard,hrel⟩ := hpoints z hz
    obtain ⟨hS₁,_⟩ := hrel
    rw [hyz] at hS₁ hcard
    exact ⟨hS₁,by simpa only [F,HomogeneousEndomorphism.iterate_degree] using hcard⟩
  obtain ⟨y,hyinj,hyrange,hyfib,hydisj,hyunion,hS,hScard⟩ :=
    finite_target_fiber_enumeration F.onPoints Z d (F.degree^r) hd hZcard hfib
  refine ⟨hd,y,hyinj,hyrange,hyfib,hydisj,hyunion,?_,?_,hS,hScard,?_⟩
  · intro x hx
    have hfxV : F.onPoints x ∈ V.zeroSet := hx.1
    rwa [← f.iterate_total_invariance V.zeroSet hV k]
  · exact projective_pulled_back_section_common_points F V
      (f.iterate_total_invariance V.zeroSet hV k) L hL w
  · letI : Fintype (F.onPoints ⁻¹' Z) := hS.fintype
    intro v hv hrep
    let y₀ := y ⟨0,hd⟩
    have hy₀ : y₀ ∈ Z := by rw [← hyrange]; exact Set.mem_range_self _
    obtain ⟨hy₀0,hynorm,hynormeq,hcard,hrel⟩ := hpoints y₀ hy₀
    obtain ⟨hS₁,hrelation⟩ := hrel
    let z₀ := normalizedProjectivePoint (fun i : Fin n => y₀.rep i.succ/y₀.rep 0)
    let S₁ := F.onPoints ⁻¹' {z₀}
    have hsub : S₁ ⊆ F.onPoints ⁻¹' Z := by
      intro x hx
      change F.onPoints x ∈ Z
      change F.onPoints x=z₀ at hx
      rw [hx]
      change (normalizedProjectivePoint (fun i : Fin n => y₀.rep i.succ/y₀.rep 0)) ∈ Z
      rw [hynormeq]
      exact hy₀
    letI : Fintype S₁ := hS₁.fintype
    obtain ⟨lam,hlam,hpoly⟩ := hrelation
      (fun x => v ⟨x.val,hsub x.property⟩)
      (fun x => hv ⟨x.val,hsub x.property⟩)
      (fun x => hrep ⟨x.val,hsub x.property⟩)
    have hpositive : 0 < Nat.card S₁ := by
      have hh : Nat.card S₁=F.degree^r := by
        simpa only [S₁,z₀,F,HomogeneousEndomorphism.iterate_degree] using hcard
      rw [hh]
      exact pow_pos (Nat.lt_trans Nat.zero_lt_one hqk) r
    have hne : S₁.Nonempty := by
      obtain ⟨hne,_⟩ := Nat.card_pos_iff.mp hpositive
      obtain ⟨x⟩ := hne
      exact ⟨x.val,x.property⟩
    obtain ⟨weights,hweights,hoff,hon,hfunctional,heval⟩ :=
      extend_point_relation_to_actual_superset (t:=r*(F.degree-1)-1) (F.onPoints ⁻¹' Z) S₁ hS hS₁
        hsub hne v lam hlam hpoly
    refine ⟨weights,hweights,?_,?_,hfunctional,heval⟩
    · intro x hx
      apply hoff x
      change F.onPoints x.val ≠ z₀
      simpa only [z₀,hynormeq] using hx
    · intro x hx
      apply hon x
      change F.onPoints x.val=z₀
      simpa only [z₀,hynormeq] using hx

end LinearStudy
