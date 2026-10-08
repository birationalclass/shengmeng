module
public import Linear.ProjectiveLinearSectionPointEquiv
public import Linear.HomogeneousPullbackComponents
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

def linearSectionSourceForms {r : ℕ} (w : Fin (r+1) → ℂ) :
    Fin r → MvPolynomial (Fin (r+1)) ℂ :=
  fun i => MvPolynomial.C (w 0)*MvPolynomial.X i.succ -
    MvPolynomial.C (w i.succ)*MvPolynomial.X 0

def projectiveLinearSectionForms {n r : ℕ} (L : Fin (r+1) → CoordinateRing n)
    (w : Fin (r+1) → ℂ) : Fin r → CoordinateRing n :=
  fun i => MvPolynomial.aeval L (linearSectionSourceForms w i)

theorem linearSectionSourceForms_linearIndependent {r : ℕ} (w : Fin (r+1) → ℂ)
    (hw : w 0 ≠ 0) : LinearIndependent ℂ (linearSectionSourceForms w) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  let v : Fin (r+1) → ℂ := Fin.cases 0 (Pi.single i 1)
  have he := congrArg (MvPolynomial.eval v) ha
  have hei : a i*w 0=0 := by
    simpa [linearSectionSourceForms,v,MvPolynomial.smul_eval,Pi.single_apply,
      mul_comm] using he
  exact (mul_eq_zero.mp hei).resolve_right hw

theorem projectiveLinearSectionForms_homogeneous {n r : ℕ}
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (i : Fin r) :
    (projectiveLinearSectionForms L w i).IsHomogeneous 1 := by
  simpa [projectiveLinearSectionForms,linearSectionSourceForms] using
    ((hL i.succ).C_mul (w 0)).sub ((hL 0).C_mul (w i.succ))

/-- Actual r independent linear defining equations, not an abstract
codimension-r subspace supplied as an assumption. -/
theorem projectiveLinearSectionForms_linearIndependent {n r : ℕ}
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (w : Fin (r+1) → ℂ) (hw : w 0 ≠ 0) :
    LinearIndependent ℂ (projectiveLinearSectionForms L w) := by
  have hL : Function.Injective (MvPolynomial.aeval L :
      MvPolynomial (Fin (r+1)) ℂ →ₐ[ℂ] CoordinateRing n) := by
    intro P Q h
    apply hinj
    exact congrArg (Ideal.Quotient.mk V.ideal.toIdeal) h
  exact (linearSectionSourceForms_linearIndependent w hw).map'
    (MvPolynomial.aeval L).toLinearMap (LinearMap.ker_eq_bot.mpr hL)

theorem projective_linear_section_defining_forms_iff {n r : ℕ}
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (w : Fin (r+1) → ℂ) (z : ProjectivePoint n) :
    z ∈ projectiveLinearSection V L w ↔
      z ∈ V.zeroSet ∧ ∀ i, MvPolynomial.eval z.rep (projectiveLinearSectionForms L w i)=0 := by
  constructor
  · rintro ⟨hz,hrel⟩
    refine ⟨hz,?_⟩
    intro i
    simpa [projectiveLinearSectionForms,linearSectionSourceForms,MvPolynomial.aeval_def,
      ← MvPolynomial.eval_assoc,mul_comm,sub_eq_zero] using hrel i.succ
  · rintro ⟨hz,heq⟩
    refine ⟨hz,?_⟩
    intro i
    cases i using Fin.cases with
    | zero => ring
    | succ i =>
      simpa [projectiveLinearSectionForms,linearSectionSourceForms,MvPolynomial.aeval_def,
        ← MvPolynomial.eval_assoc,mul_comm,sub_eq_zero] using heq i

/-- Homogeneous pullback vanishing is compared at the ACTUAL projective
image point, including its representative scaling. -/
theorem homogeneous_pullback_vanish_iff_onPoints {n D : ℕ}
    (f : HomogeneousEndomorphism n) (P : CoordinateRing n) (hP : P.IsHomogeneous D)
    (x : ProjectivePoint n) :
    MvPolynomial.eval x.rep (MvPolynomial.aeval f.forms P)=0 ↔
      MvPolynomial.eval (f.onPoints x).rep P=0 := by
  have hx := Projectivization.rep_nonzero x
  have hfx : f.onPoints x = Projectivization.mk ℂ (f.evalVector x.rep) (f.noBasePoint x.rep hx) := by
    simpa only [Projectivization.mk_rep] using (f.onPoints_mk x.rep hx)
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (f.evalVector x.rep)
    (f.noBasePoint x.rep hx)
  rw [hfx,←ha,Units.smul_def,homogeneous_eval_smul hP]
  have he : MvPolynomial.eval x.rep (MvPolynomial.aeval f.forms P) =
      MvPolynomial.eval (f.evalVector x.rep) P := by
    exact (MvPolynomial.eval_assoc f.forms x.rep P).symm
  rw [he]
  simp [(a.isUnit.ne_zero),pow_ne_zero D a.isUnit.ne_zero]

/-- Common zeros of the actual degree-q pullbacks are EXACTLY the preimage
of the actual linear section on original V, at the projective POINT level.
This does not assert equality of nonreduced schemes. -/
theorem projective_pulled_back_section_common_points {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) :
    {x : ProjectivePoint n | x ∈ V.zeroSet ∧ ∀ i,
      MvPolynomial.eval x.rep (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))=0} =
      f.onPoints ⁻¹' projectiveLinearSection V L w := by
  ext x
  change (x ∈ V.zeroSet ∧ _) ↔ f.onPoints x ∈ projectiveLinearSection V L w
  rw [projective_linear_section_defining_forms_iff]
  have hinv : f.onPoints x ∈ V.zeroSet ↔ x ∈ V.zeroSet := by
    change x ∈ f.onPoints ⁻¹' V.zeroSet ↔ x ∈ V.zeroSet
    rw [hV]
  rw [hinv]
  apply and_congr_right
  intro hx
  exact forall_congr' (fun i => homogeneous_pullback_vanish_iff_onPoints f _
    (projectiveLinearSectionForms_homogeneous L hL w i) x)

theorem projective_pulled_back_section_forms_homogeneous {n r : ℕ}
    (f : HomogeneousEndomorphism n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1) (w : Fin (r+1) → ℂ) (i : Fin r) :
    (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)).IsHomogeneous f.degree := by
  simpa only [mul_one] using
    (projectiveLinearSectionForms_homogeneous L hL w i).aeval f.forms f.homogeneous

/-- The actual common point set is the union of the ACTUAL whole original
fibers, indexed by actual targets of the linear section. -/
theorem projective_pulled_back_section_common_points_eq_fiber_union {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) :
    {x : ProjectivePoint n | x ∈ V.zeroSet ∧ ∀ i,
      MvPolynomial.eval x.rep (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))=0} =
      ⋃ z : projectiveLinearSection V L w, f.onPoints ⁻¹' {z.val} := by
  rw [projective_pulled_back_section_common_points f V hV L hL w]
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion.mpr ⟨⟨f.onPoints x,hx⟩,rfl⟩
  · intro hx
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp hx
    change f.onPoints x=z.val at hz
    change f.onPoints x ∈ projectiveLinearSection V L w
    rw [hz]
    exact z.property

end LinearStudy
