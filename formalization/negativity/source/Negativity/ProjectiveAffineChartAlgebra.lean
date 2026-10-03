module

public import Negativity.RelativeProjectiveEmbedding
public import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open HomogeneousLocalization
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev actualProjectiveAffineChart (R : Type u) [CommRing R] (n : ℕ) :=
  Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X (0 : Fin (n + 1)))

def actualProjectiveChartConstant (R : Type u) [CommRing R] (n : ℕ) :
    R →+* actualProjectiveAffineChart R n :=
  (fromZeroRingHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) _).comp
    (projectiveDegreeZeroInclusion R n)

def actualProjectiveChartCoordinate (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin n) : actualProjectiveAffineChart R n :=
  Away.mk _ (MvPolynomial.isHomogeneous_X R (0 : Fin (n + 1))) 1
    (MvPolynomial.X i.succ) (by simpa using MvPolynomial.isHomogeneous_X R i.succ)

def actualProjectiveChartEvaluation {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] {n : ℕ} (g : MvPolynomial (Fin n) R →ₐ[R] B) :
    actualProjectiveAffineChart R n →+* B := by
  let e : MvPolynomial (Fin (n + 1)) R →+* B :=
    MvPolynomial.eval₂Hom (algebraMap R B) (Fin.cases 1 (fun i => g (MvPolynomial.X i)))
  have he : IsUnit (e (MvPolynomial.X (0 : Fin (n + 1)))) := by
    simp [e]
  exact (Localization.awayLift e (MvPolynomial.X (0 : Fin (n + 1))) he).comp
    (algebraMap (actualProjectiveAffineChart R n)
      (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial _ R)))

theorem actual_projective_chart_evaluation_constant
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} (g : MvPolynomial (Fin n) R →ₐ[R] B) (r : R) :
    actualProjectiveChartEvaluation g (actualProjectiveChartConstant R n r) =
      algebraMap R B r := by
  let e : MvPolynomial (Fin (n + 1)) R →+* B :=
    MvPolynomial.eval₂Hom (algebraMap R B) (Fin.cases 1 (fun i => g (MvPolynomial.X i)))
  have he : e (MvPolynomial.X (0 : Fin (n + 1))) * 1 = 1 := by simp [e]
  change Localization.awayLift e _ (isUnit_iff_exists_inv.mpr ⟨1, he⟩)
    (Localization.mk (MvPolynomial.C r) ⟨_, 0, rfl⟩) = _
  rw [Localization.awayLift_mk e _ (MvPolynomial.C r) 1 he 0]
  simp [e]

theorem actual_projective_chart_evaluation_coordinate
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} (g : MvPolynomial (Fin n) R →ₐ[R] B) (i : Fin n) :
    actualProjectiveChartEvaluation g (actualProjectiveChartCoordinate R n i) =
      g (MvPolynomial.X i) := by
  let e : MvPolynomial (Fin (n + 1)) R →+* B :=
    MvPolynomial.eval₂Hom (algebraMap R B) (Fin.cases 1 (fun i => g (MvPolynomial.X i)))
  have he : e (MvPolynomial.X (0 : Fin (n + 1))) * 1 = 1 := by simp [e]
  change Localization.awayLift e _ (isUnit_iff_exists_inv.mpr ⟨1, he⟩)
    (Localization.mk (MvPolynomial.X i.succ) ⟨MvPolynomial.X 0 ^ 1, _⟩) = _
  rw [Localization.awayLift_mk e _ (MvPolynomial.X i.succ) 1 he 1]
  simp [e]

/-- Final theorem: every actual finite-type algebra is a quotient of an
actual standard projective affine-chart ring, with its genuine base-ring
map respected. The quotient is constructed from polynomial generators;
no projective embedding or chart surjectivity is an input. -/
theorem exists_actual_projective_affine_chart_quotient
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] :
    ∃ (n : ℕ) (φ : actualProjectiveAffineChart R n →+* B),
      Function.Surjective φ ∧
      φ.comp (actualProjectiveChartConstant R n) = algebraMap R B := by
  obtain ⟨n, g, hg⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := B)).mp
    (inferInstanceAs (Algebra.FiniteType R B))
  let φ := actualProjectiveChartEvaluation g
  let t : MvPolynomial (Fin n) R →+* actualProjectiveAffineChart R n :=
    MvPolynomial.eval₂Hom (actualProjectiveChartConstant R n)
      (actualProjectiveChartCoordinate R n)
  have ht : φ.comp t = g.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa [φ, t] using actual_projective_chart_evaluation_constant g r
    · intro i
      simpa [φ, t] using actual_projective_chart_evaluation_coordinate g i
  refine ⟨n, φ, ?_, ?_⟩
  · intro b
    obtain ⟨p, hp⟩ := hg b
    refine ⟨t p, ?_⟩
    change (φ.comp t) p = b
    rw [ht]
    exact hp
  · ext r
    exact actual_projective_chart_evaluation_constant g r

end
end Negativity
