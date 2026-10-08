module
public import Linear.ProjectiveCoordinateRatioMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Actual homogeneous scaling, used to separate the cone coordinate
from the projective coordinate-ratio field. -/
def HomogeneousEndomorphism.scaling (n : ℕ) (u : ℂˣ) : HomogeneousEndomorphism n where
  degree := 1
  forms := fun i => (u : ℂ) • MvPolynomial.X i
  homogeneous := fun i =>
    ((MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ) 1).smul_mem
      (u : ℂ) (MvPolynomial.isHomogeneous_X ℂ i)
  noBasePoint := by
    intro v hv
    have he : (fun i : Fin (n + 1) => MvPolynomial.eval v ((u : ℂ) • MvPolynomial.X i)) =
        (u : ℂ) • v := by
      funext i
      simp
    rw [he]
    exact smul_ne_zero (Units.ne_zero u) hv

theorem HomogeneousEndomorphism.scaling_evalVector (u : ℂˣ) (v : CoordinateVector n) :
    (scaling n u).evalVector v = (u : ℂ) • v := by
  funext i
  simp [scaling, evalVector]

theorem HomogeneousEndomorphism.scaling_onPoints (u : ℂˣ) :
    (scaling n u).onPoints = id := by
  funext x
  induction x using Projectivization.ind with
  | h v hv =>
    rw [onPoints_mk]
    apply (Projectivization.mk_eq_mk_iff ℂ _ v _ hv).mpr
    exact ⟨u, by simpa only [Units.smul_def] using (scaling_evalVector u v).symm⟩

def projectiveConeScalingMap (V : IntegralProjectiveEquations n) (u : ℂˣ) :
    letI := V.prime
    FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal) →ₐ[ℂ]
      FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal) := by
  letI := V.prime
  have hf : Function.Surjective (HomogeneousEndomorphism.scaling n u).onPoints := by
    rw [HomogeneousEndomorphism.scaling_onPoints]
    exact Function.surjective_id
  have hV : (HomogeneousEndomorphism.scaling n u).onPoints ⁻¹' V.zeroSet = V.zeroSet := by
    rw [HomogeneousEndomorphism.scaling_onPoints]
    rfl
  exact projectiveCoordinateFractionMap (HomogeneousEndomorphism.scaling n u) V
    (by change 0 < (1 : ℕ); decide) hf hV

theorem projectiveConeScalingMap_coordinate
    (V : IntegralProjectiveEquations n) (u : ℂˣ) (i : Fin (n + 1)) :
    letI := V.prime
    projectiveConeScalingMap V u (projectiveConeFractionCoordinates V i) =
      algebraMap ℂ (FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal)) (u : ℂ) *
        projectiveConeFractionCoordinates V i := by
  letI := V.prime
  unfold projectiveConeScalingMap
  rw [projectiveCoordinateFractionMap_coordinate]
  simp [HomogeneousEndomorphism.scaling, Algebra.smul_def]

end LinearStudy
