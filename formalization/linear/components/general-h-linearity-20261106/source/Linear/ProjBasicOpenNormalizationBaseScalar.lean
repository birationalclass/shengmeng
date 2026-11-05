module
public import Linear.ProjBasicOpenBaseScalar
public import Linear.NormalizationChartConstants
public import Linear.SemilinearComparisonScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
/-- The ORIGINAL source base-global scalar equals the original normalization-chart scalar.
Only scalar rings occur;no coefficient module or duality square is assumed. -/
theorem projBasicOpenBaseScalar_eq_normalizationChart
    {d : ℕ} (a : R) (ha : a ∈ A d) (hd : 0<d)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :
    projBasicOpenBaseScalar B (algebraMap K (B 0)) (algebraMap R S a) r =
      ((Proj.awayToSection B (algebraMap R S a)).hom.comp
        (normalizationHomogeneousChartMap A B a))
        (HomogeneousLocalization.fromZeroRingHom A (Submonoid.powers a)
          (algebraMap K (A 0) ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r))) := by
  rw [projBasicOpenBaseScalar_eq_chart B (algebraMap K (B 0)) (algebraMap R S a)
    ((normalizationBaseGradedRingHom A B).map_mem ha) hd r]
  exact (congrArg (fun v => (Proj.awayToSection B (algebraMap R S a)).hom v)
    (normalizationHomogeneousChartMap_baseConstant A B a
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r))).symm
end LinearStudy
