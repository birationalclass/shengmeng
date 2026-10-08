module
public import Linear.LinearProjectionFiberPointEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective linear section in the original V cut out by
the homogeneous linear equations w0 Li - wi L0 = 0. -/
def projectiveLinearSection {n r : ℕ} (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) :
    Set (ProjectivePoint n) :=
  {p | p ∈ V.zeroSet ∧ ∀ i,
    MvPolynomial.eval p.rep (L i) * w 0 = w i * MvPolynomial.eval p.rep (L 0)}

theorem linear_projection_coordinate_fiber_nonzero {n r : ℕ}
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (hw0 : w 0 ≠ 0)
    (v : CoordinateVector n) (hvL : (fun i => MvPolynomial.eval v (L i)) = w) :
    v ≠ 0 := by
  intro hv
  have he := congrFun hvL 0
  have hzero : MvPolynomial.eval (0 : CoordinateVector n) (L 0) = 0 := by
    simpa using homogeneous_eval_smul (hL 0) (0 : ℂ) (0 : CoordinateVector n)
  rw [hv,hzero] at he
  exact hw0 he.symm

/-- Actual cone fiber points and actual projective linear section
points are bijective. Homogeneity and the already derived no-basepoint
property prove that normalization is possible and unique. -/
theorem projective_linear_section_coordinate_point_equiv {n r : ℕ}
    (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfree : ∀ (v : CoordinateVector n), v ≠ 0 →
      (∀ H ∈ V.ideal.toIdeal, MvPolynomial.eval v H = 0) →
      (fun i => MvPolynomial.eval v (L i)) ≠ 0)
    (w : Fin (r+1) → ℂ) (hw0 : w 0 ≠ 0) :
    Nonempty ({v : MvPolynomial.zeroLocus ℂ V.ideal.toIdeal //
      (fun i => MvPolynomial.eval v.1 (L i)) = w} ≃ projectiveLinearSection V L w) := by
  classical
  let j : {v : MvPolynomial.zeroLocus ℂ V.ideal.toIdeal //
      (fun i => MvPolynomial.eval v.1 (L i)) = w} → projectiveLinearSection V L w := fun v => by
    have hv := linear_projection_coordinate_fiber_nonzero L hL w hw0 v.1.1 v.2
    refine ⟨Projectivization.mk ℂ v.1.1 hv, (V.mem_zeroSet_mk _ hv).mpr v.1.2,?_⟩
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1.1 hv
    intro i
    rw [←ha]
    simp only [Units.smul_def,homogeneous_eval_smul (hL i),
      homogeneous_eval_smul (hL 0),pow_one,congrFun v.2 i,congrFun v.2 0]
    ring
  have hinj : Function.Injective j := by
    intro v u h
    have hv := linear_projection_coordinate_fiber_nonzero L hL w hw0 v.1.1 v.2
    have hu := linear_projection_coordinate_fiber_nonzero L hL w hw0 u.1.1 u.2
    have hmk : Projectivization.mk ℂ v.1.1 hv = Projectivization.mk ℂ u.1.1 hu :=
      congrArg Subtype.val h
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hmk
    have he := congrArg (fun z : CoordinateVector n => MvPolynomial.eval z (L 0)) ha
    have he0 : (a : ℂ) * w 0 = w 0 := by
      simpa only [Units.smul_def,homogeneous_eval_smul (hL 0),pow_one,
        congrFun u.2 0,congrFun v.2 0] using he
    have ha1 : (a : ℂ) = 1 := mul_right_cancel₀ hw0 (he0.trans (one_mul (w 0)).symm)
    have haUnit : a = 1 := Units.ext ha1
    rw [haUnit,one_smul] at ha
    apply Subtype.ext
    apply Subtype.ext
    exact ha.symm
  have hsurj : Function.Surjective j := by
    intro p
    let v := p.1.rep
    have hv : v ≠ 0 := Projectivization.rep_nonzero p.1
    have hV : ∀ H ∈ V.ideal.toIdeal, MvPolynomial.eval v H = 0 := p.2.1
    have hrel (i) : MvPolynomial.eval v (L i) * w 0 = w i * MvPolynomial.eval v (L 0) := p.2.2 i
    have hL0 : MvPolynomial.eval v (L 0) ≠ 0 := by
      intro hz
      apply hfree v hv hV
      funext i
      have hi := hrel i
      rw [hz,mul_zero] at hi
      exact (mul_eq_zero.mp hi).resolve_right hw0
    let b : ℂ := w 0 / MvPolynomial.eval v (L 0)
    have hb : b ≠ 0 := div_ne_zero hw0 hL0
    have hzV : b • v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal :=
      homogeneous_zeroLocus_smul V.ideal.toIdeal V.ideal.isHomogeneous v hV b
    have hzL : (fun i => MvPolynomial.eval (b • v) (L i)) = w := by
      funext i
      rw [homogeneous_eval_smul (hL i),pow_one]
      dsimp [b]
      field_simp [hL0]
      simpa only [mul_comm] using hrel i
    refine ⟨⟨⟨b • v,hzV⟩,hzL⟩,?_⟩
    apply Subtype.ext
    change Projectivization.mk ℂ (b • v) _ = p.1
    rw [← Projectivization.mk_rep p.1]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨b,rfl⟩
  exact ⟨Equiv.ofBijective j ⟨hinj,hsurj⟩⟩

/-- The original V has ACTUAL generic projective linear sections whose
cardinality is the generic rank of its constructed linear normalization.
The remaining bridge is this rank's equality with degree V. -/
theorem projective_exists_linear_projection_section_card {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := V.prime
    ∃ (r : ℕ) (P : Polynomial ℚ), r ≤ n ∧ P ≠ 0 ∧ P.natDegree = r ∧
      (∃ N : ℕ, ∀ m > N, P.eval (m : ℚ) =
        (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        let R := MvPolynomial (Fin (r+1)) ℂ
        let A := CoordinateRing n ⧸ V.ideal.toIdeal
        let φ := projectiveLinearNormalizationMap V L
        letI : Algebra R A := φ.toRingHom.toAlgebra
        letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
        letI : Module R A := Algebra.toModule
        ∃ c : R, c ≠ 0 ∧
          (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
          ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
            w 0 ≠ 0 ∧ Nat.card (projectiveLinearSection V L w) = Module.finrank R A := by
  classical
  letI := V.prime
  obtain ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,hfree,c,hc,hex,hfib⟩ :=
    projective_exists_linear_projection_cone_fiber_card V
  refine ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hcard⟩ := hfib w hw
  obtain ⟨e⟩ := projective_linear_section_coordinate_point_equiv V L hL hfree w hw0
  exact ⟨hw0,(Nat.card_congr e).symm.trans hcard⟩

end LinearStudy
