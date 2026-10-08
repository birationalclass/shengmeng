module
public import Linear.ProjectiveWholeFiberGoodDimension
public import Linear.ProjectiveWholeFiberPointLoci
public import Linear.ProjectiveSmoothCommonDimension
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Explicit output data on the ACTUAL whole affine fiber equation set.
All finite types, point membership, local smoothness, common equations and
formal original-ideal identifications are constructed by the theorem below.
This definition is an output statement, not a final theorem or an input axiom. -/
def ProjectiveWholeFiberCommonCoordinateConclusion
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet) (r : ℕ) : Prop :=
    let S := MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)
    let hx : ∀ a : S, normalizedProjectivePoint a.val ∈ V.zeroSet :=
      fun a => (projectiveAffineFiberIdeal_point f V y a.val a.property).1
    ∃ hS : S.Finite,
      letI : Fintype S := hS.fintype
      ∃ hSne : Nonempty S,
      letI : Nonempty S := hSne
      Nat.card S = f.degree ^ r ∧
      (∀ a : S, Algebra.IsSmoothAt ℂ (V.affinePoint a.val (hx a)).asIdeal) ∧
      Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal ∧
      ∃ c : ℕ, c = n - r ∧
        ProjectiveCommonNormalPresentation V (fun a : S => a.val) hx r c

/-- SAME original whole fiber: its exact q^r point count, ALL smooth source
points, the SAME smooth target, and ONE actual ambient linear coordinate
system with local generators and formal normal ideals. This is constructed
for EVERY original iterate on a nonempty open. No fiber or local equations
are supplied, and no independent abstract point family replaces the fiber. -/
theorem projective_iterates_whole_fibers_actual_common_coordinates
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) = r ∧
      ∀ k : ℕ,
        let F := f.iterate k
        let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
        let A := Localization.Away (projectiveChartDenominator F V)
        let φ := projectiveChartOpenMap F V (f.iterate_degree_pos hq k)
          (f.iterate_surjective hf k) (f.iterate_total_invariance V.zeroSet hV k) x0 hx0
        letI : Algebra B A := φ.toRingHom.toAlgebra
        ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
        (∀ P : PrimeSpectrum A, φ (Ideal.Quotient.mk V.affineIdeal p) ∉ P.asIdeal →
          P ∈ Algebra.smoothLocus ℂ A ∧
          PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
          P ∈ Algebra.unramifiedLocus B A) ∧
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 →
          (∀ (v : CoordinateVector n) (hv : v ≠ 0),
            (f.iterate k).onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) ∧
          ProjectiveWholeFiberCommonCoordinateConclusion (f.iterate k) V y hy r := by
  classical
  obtain ⟨r, hrn, hdim, hrank, _, hiter⟩ :=
    projective_iterates_whole_good_fibers_same_dimension f V hq hf hV hproper x0 hx0
  refine ⟨r, hrn, hdim, hrank, ?_⟩
  intro k F B A φ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨p, hp, hgood, hnonempty, hfiber⟩ := hiter k
  refine ⟨p, hp, hgood, hnonempty, ?_⟩
  intro y hy hyp
  obtain ⟨_, hchart, _, _, hcard⟩ := hfiber y hy hyp
  refine ⟨hchart, ?_⟩
  unfold ProjectiveWholeFiberCommonCoordinateConclusion
  intro S hx
  have hS := projectiveAffineFiberIdeal_zeroLocus_finite F V (f.iterate_degree_pos hq k) y
  letI : Fintype S := hS.fintype
  obtain ⟨E⟩ := projectiveAffineFiber_nonempty_whole_point_equiv F V y hy
    (f.iterate_total_invariance V.zeroSet hV k) hchart
  obtain ⟨w, hw⟩ := f.iterate_surjective hf k (normalizedProjectivePoint y)
  letI : Nonempty (F.onPoints ⁻¹' {normalizedProjectivePoint y}) := ⟨⟨w, hw⟩⟩
  have hSne : Nonempty S := Nonempty.map E.symm inferInstance
  letI : Nonempty S := hSne
  have hs : ∀ a : S, Algebra.IsSmoothAt ℂ (V.affinePoint a.val (hx a)).asIdeal := by
    intro a
    have hfy := (projectiveAffineFiberIdeal_point F V y a.val a.property).2.2
    obtain ⟨_, hs, _, _, _⟩ := projective_whole_fiber_point_actual_good_loci F V
      (f.iterate_degree_pos hq k) (f.iterate_surjective hf k)
      (f.iterate_total_invariance V.zeroSet hV k) x0 hx0 p hgood y a.val hy (hx a) hyp hfy
    exact hs
  letI : ∀ a : S, Algebra.IsSmoothAt ℂ (V.affinePoint a.val (hx a)).asIdeal := hs
  have ht : Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal := by
    let a : S := Classical.arbitrary S
    have hfy := (projectiveAffineFiberIdeal_point F V y a.val a.property).2.2
    obtain ⟨_, _, ht, _, _⟩ := projective_whole_fiber_point_actual_good_loci F V
      (f.iterate_degree_pos hq k) (f.iterate_surjective hf k)
      (f.iterate_total_invariance V.zeroSet hV k) x0 hx0 p hgood y a.val hy (hx a) hyp hfy
    exact ht
  have hScard : Nat.card S = F.degree ^ r := by
    rw [Nat.card_congr E, hcard, f.iterate_degree]
  obtain ⟨s, c, _, hsrank, hcr, hc, e, M, hM, G, h⟩ :=
    projective_smooth_points_common_coordinates_actual_dimension V hproper (fun a : S => a.val) hx
  have hsr : s = r := hsrank.symm.trans hrank
  clear hsrank
  subst s
  exact ⟨hS, hSne, hScard, hs, ht, c, hcr, hc, e, M, hM, G, h⟩

end LinearStudy
