module
public import Linear.ProjectiveWholeFiberHomogeneousRelation
public import Linear.ProjectiveNormalizedConePoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An arbitrary actual representative of a normalized projective point
automatically has nonzero coordinate zero and the original affine ratios. -/
theorem normalizedProjectivePoint_representative_coordinates {n : ℕ}
    (x : Fin n → ℂ) (v : CoordinateVector n) (hv : v ≠ 0)
    (hrep : Projectivization.mk ℂ v hv = normalizedProjectivePoint x) :
    v 0 ≠ 0 ∧ (fun i : Fin n => v i.succ / v 0) = x := by
  change Projectivization.mk ℂ v hv = Projectivization.mk ℂ (Fin.cases (1 : ℂ) x)
    (normalizedCoordinateVector_ne_zero x) at hrep
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ v (Fin.cases (1 : ℂ) x) hv
    (normalizedCoordinateVector_ne_zero x)).mp hrep
  have h0 : a = v 0 := by simpa [Pi.smul_apply,smul_eq_mul] using congrFun ha 0
  have ha0 : a ≠ 0 := by
    intro h
    apply hv
    rw [← ha,h,zero_smul]
  have hv0 : v 0 ≠ 0 := by
    rw [← h0]
    exact ha0
  refine ⟨hv0,?_⟩
  exact normalizedProjectivePoint_injective
    ((normalizedProjectivePoint_coordinate_ratios v hv hv0).trans hrep)

/-- Change from normalized vectors to any actual chosen representatives.
Nonzero coefficients survive the exact homogeneous scaling factor. -/
theorem homogeneous_normalized_relation_representatives
    {n : ℕ} {ι : Type*} [Fintype ι] (x : ι → Fin n → ℂ)
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (t : ℕ)
    (hrel : ∀ P : MvPolynomial (Fin (n+1)) ℂ, P.IsHomogeneous t →
      ∑ i, lam i * MvPolynomial.eval (Fin.cases 1 (x i)) P = 0)
    (v : ι → CoordinateVector n) (hv : ∀ i, v i ≠ 0)
    (hrep : ∀ i, Projectivization.mk ℂ (v i) (hv i) = normalizedProjectivePoint (x i)) :
    ∃ weights : ι → ℂ, (∀ i, weights i ≠ 0) ∧
      ∀ P : MvPolynomial (Fin (n+1)) ℂ, P.IsHomogeneous t →
        ∑ i, weights i * MvPolynomial.eval (v i) P = 0 := by
  have hcoords := fun i => normalizedProjectivePoint_representative_coordinates
    (x i) (v i) (hv i) (hrep i)
  refine ⟨fun i => lam i/(v i 0)^t,fun i => div_ne_zero (hlam i) (pow_ne_zero t (hcoords i).1),?_⟩
  intro P hP
  convert hrel P hP using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [homogeneous_affine_chart_eval P hP (v i) (hcoords i).1,
      (hcoords i).2,affineDehomogenize_eval]
  field_simp [(hcoords i).1]

/-- The original single-whole-fiber relation in the manuscript's arbitrary
coordinate-representative convention. Only its already proved normalized
output is supplied, not a new residue or degree hypothesis. -/
theorem projective_whole_fiber_arbitrary_representative_relation {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ)
    (hrel : ProjectiveWholeFiberHomogeneousRelationConclusion f V y r) :
    let S := MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)
    ∃ hS : S.Finite,
      letI : Fintype S := hS.fintype
      ∀ (v : S → CoordinateVector n) (hv : ∀ x, v x ≠ 0),
        (∀ x, Projectivization.mk ℂ (v x) (hv x) = normalizedProjectivePoint x.val) →
        ∃ weights : S → ℂ, (∀ x, weights x ≠ 0) ∧
          ∀ P : MvPolynomial (Fin (n+1)) ℂ, P.IsHomogeneous (r*(f.degree-1)-1) →
            ∑ x : S, weights x * MvPolynomial.eval (v x) P = 0 := by
  intro S
  obtain ⟨hS,lam,hlam,hrel⟩ := hrel
  refine ⟨hS,?_⟩
  letI : Fintype S := hS.fintype
  intro v hv hrep
  exact homogeneous_normalized_relation_representatives (fun x : S => x.val)
    lam hlam (r*(f.degree-1)-1) hrel v hv hrep

/-- Every original iterate derives the manuscript's relation for any
chosen nonzero representatives, not merely for normalized ones.
The positive-dimensional good-open and degree scopes stay explicit. -/
theorem projective_iterates_whole_fibers_representative_relations {n : ℕ}
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
            (let S := MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal (f.iterate k) V y)
             ∃ hS : S.Finite,
               letI : Fintype S := hS.fintype
               ∀ (v : S → CoordinateVector n) (hv : ∀ x, v x ≠ 0),
                 (∀ x, Projectivization.mk ℂ (v x) (hv x) = normalizedProjectivePoint x.val) →
                 ∃ weights : S → ℂ, (∀ x, weights x ≠ 0) ∧
                   ∀ P : MvPolynomial (Fin (n+1)) ℂ,
                     P.IsHomogeneous (r*((f.iterate k).degree-1)-1) →
                     ∑ x : S, weights x * MvPolynomial.eval (v x) P = 0) := by
  obtain ⟨r,hrn,hdim,hrank,hiter⟩ := projective_iterates_whole_fibers_homogeneous_relations
    f V hq hf hV hproper x0 hx0
  refine ⟨r,hrn,hdim,hrank,?_⟩
  intro k
  obtain ⟨p,hp,hnonempty,hfiber⟩ := hiter k
  refine ⟨p,hp,hnonempty,?_⟩
  intro y hy hyp hr hqk
  obtain ⟨hgeom,hrel⟩ := hfiber y hy hyp hr hqk
  exact ⟨hgeom,projective_whole_fiber_arbitrary_representative_relation
    (f.iterate k) V y hrel⟩

end LinearStudy
