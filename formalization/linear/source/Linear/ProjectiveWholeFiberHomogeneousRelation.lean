module
public import Linear.ProjectiveWholeFiberJacobianSystem
public import Linear.PolynomialZeroLocusResidueRelation
public import Linear.PolynomialCoordinateZeroLocusEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4800000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ORIGINAL whole in-V fiber and ORIGINAL homogeneous polynomials.
Coordinates of each vector are normalized with coordinate zero equal to one.
This is an output statement, not a new geometric input. -/
def ProjectiveWholeFiberHomogeneousRelationConclusion {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ) (r : ℕ) : Prop :=
  let S := MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)
  ∃ hS : S.Finite,
    letI : Fintype S := hS.fintype
    ∃ lam : S → ℂ, (∀ x, lam x ≠ 0) ∧
      ∀ σ : MvPolynomial (Fin (n+1)) ℂ, σ.IsHomogeneous (r*(f.degree-1)-1) →
        ∑ x : S, lam x * MvPolynomial.eval (Fin.cases 1 x.val) σ = 0

/-- Insert the SAME original whole-fiber equation/Jacobian system into the
actual residue pairing, transport back through the actual source algebra
equivalence and dehomogenize the ORIGINAL homogeneous polynomials.
No local socle, residue relation, transformed highest or degree assumption
is added beyond the already constructed geometric outputs. -/
theorem projective_actual_whole_fiber_homogeneous_relation {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hr : 0 < r) (hq : 1 < f.degree)
    (hgeom : ProjectiveWholeAmbientFiberConclusion f V y hy r)
    (hSystem : ProjectiveWholeFiberJacobianSystemConclusion f y r) :
    ProjectiveWholeFiberHomogeneousRelationConclusion f V y r := by
  classical
  obtain ⟨c,hcr,hc,eS,MS,hMS,eT,MT,hMT,hFinite,hle,hTop,hbound,hgen⟩ := hSystem
  have hcard : r+c=n := by simpa using Fintype.card_congr eS
  cases n with
  | zero => omega
  | succ N =>
    let E := (polynomialLinearChangeEquiv MS hMS).trans (MvPolynomial.renameEquiv ℂ eS.symm)
    let z := MT⁻¹ *ᵥ (y ∘ eT)
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
      fun j => E (affineChartPolynomialMap (f.forms (eT j).succ))
    let pC : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
      fun i => MvPolynomial.aeval p ((MT⁻¹).toMvPolynomial i) - MvPolynomial.C (z i) * p0
    let J := Ideal.span (Set.range pC)
    let A := MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ J
    let Θ : MvPolynomial (Fin r ⊕ Fin c) ℂ :=
      Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (pC (Sum.inr i)))
    let I := projectiveAmbientFiberIdeal f y
    let S := MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)
    have hq0 : 0 < f.degree := lt_trans Nat.zero_lt_one hq
    have hS : S.Finite := projectiveAffineFiberIdeal_zeroLocus_finite f V hq0 y
    letI : Fintype S := hS.fintype
    letI : Module.Finite ℂ A := hFinite
    letI : Fintype (MvPolynomial.zeroLocus ℂ J) :=
      (polynomial_zeroLocus_finite_of_module_finite J).fintype
    have hJ : J = I.map E.toRingHom :=
      projective_actual_centered_fiber_ideal f y E eT.symm MT hMT
    let E0 : S ≃ MvPolynomial.zeroLocus ℂ I :=
      { toFun := fun x => ⟨x.val,by rw [hgeom.2.2.1];exact x.property⟩
        invFun := fun x => ⟨x.val,by
          change x.val ∈ MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)
          rw [← hgeom.2.2.1]
          exact x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let EP := polynomialCoordinateZeroLocusEquiv E I J hJ
    let ES := E0.trans EP
    obtain ⟨lam,hlam,hrel⟩ := polynomial_zeroLocus_weighted_relation eS pC hq0 hle hTop Θ hgen
    have hEdegree (F : MvPolynomial (Fin (N+1)) ℂ) :
        (E F).totalDegree = F.totalDegree := by
      change (MvPolynomial.renameEquiv ℂ eS.symm (polynomialLinearChangeEquiv MS hMS F)).totalDegree =
        F.totalDegree
      rw [MvPolynomial.totalDegree_renameEquiv,polynomialLinearChangeEquiv_totalDegree]
    have hthreshold : c*(f.degree-1)+(r*(f.degree-1)-1) < (N+1)*(f.degree-1) := by
      have hrp : 0 < r*(f.degree-1) := Nat.mul_pos hr (Nat.sub_pos_of_lt hq)
      calc
        c*(f.degree-1)+(r*(f.degree-1)-1) <
            c*(f.degree-1)+r*(f.degree-1) :=
          Nat.add_lt_add_left (Nat.sub_lt hrp Nat.zero_lt_one) _
        _ = (r+c)*(f.degree-1) := by ring
        _ = (N+1)*(f.degree-1) := congrArg (fun a : ℕ => a*(f.degree-1)) hcard
    have hOriginal (F : MvPolynomial (Fin (N+1)) ℂ)
        (hF : F.totalDegree ≤ r*(f.degree-1)-1) :
        ∑ x : S, lam (ES x) * MvPolynomial.eval x.val F = 0 := by
      have hsmall : Θ.totalDegree + (E F).totalDegree < (N+1)*(f.degree-1) := by
        rw [hEdegree]
        exact (Nat.add_le_add hbound hF).trans_lt hthreshold
      have hh := hrel (E F) hsmall
      rw [← ES.sum_comp (fun x => lam x * MvPolynomial.eval x.val (E F))] at hh
      calc
        (∑ x : S, lam (ES x) * MvPolynomial.eval x.val F) =
            ∑ x : S, lam (ES x) * MvPolynomial.eval (ES x).val (E F) := by
          apply Finset.sum_congr rfl
          intro x _
          apply congrArg (fun a => lam (ES x)*a)
          exact (polynomialCoordinateZeroLocusEquiv_evaluation E I J hJ (E0 x) F).symm
        _ = 0 := hh
    refine ⟨hS,fun x => lam (ES x),fun x => hlam _,?_⟩
    intro σ hσ
    have hh := hOriginal (affineDehomogenize σ)
      ((affineDehomogenize_degree σ).trans hσ.totalDegree_le)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro x _
    exact congrArg (fun a => lam (ES x)*a) (affineDehomogenize_eval σ x.val).symm

/-- EVERY original iterate constructs a nonempty good open and the
ORIGINAL homogeneous whole-fiber relation in positive actual dimension.
The iterate must have degree greater than one. Simultaneous Bertini
selection of several target fibers and Section 4 are still not claimed. -/
theorem projective_iterates_whole_fibers_homogeneous_relations {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) = r ∧
      ∀ k : ℕ,
        ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 → 0 < r → 1 < (f.iterate k).degree →
          ProjectiveWholeAmbientFiberConclusion (f.iterate k) V y hy r ∧
            ProjectiveWholeFiberHomogeneousRelationConclusion (f.iterate k) V y r := by
  obtain ⟨r,hrn,hdim,hrank,hiter⟩ := projective_iterates_whole_fibers_jacobian_system
    f V hq hf hV hproper x0 hx0
  refine ⟨r,hrn,hdim,hrank,?_⟩
  intro k
  obtain ⟨p,hp,hnonempty,hfiber⟩ := hiter k
  refine ⟨p,hp,hnonempty,?_⟩
  intro y hy hyp hr hqk
  obtain ⟨hgeom,hSystem⟩ := hfiber y hy hyp hr
  exact ⟨hgeom,projective_actual_whole_fiber_homogeneous_relation (f.iterate k) V y hy
    hr hqk hgeom hSystem⟩

end LinearStudy
