module
public import Linear.ActualAffineAlgebraDualInternalHomValues
public import Linear.NativeDualGlobalHomWeightedOverlapLinear
public import Linear.NativeNormalizationGlobalWeightedAffineHomLinear
public import Linear.NativeNormalizationWeightedOverlapDualEquiv
public import Linear.NativeDualFullSourceChartEquiv
public import Linear.CoextensionBaseGradeCompatibility
public import Linear.NormalizationHomogeneousAffineDualOverlapLocalization
public import Mathlib.Algebra.Module.Torsion.Pi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  normalizationHomogeneousSourceChartAlgebra

/-- In the actual overlap affine chart, the SAME global Hom comparison
has exactly the original weighted native-dual tilde functional. -/
theorem nativeDualGlobalHomWeightedOverlapLinearEquiv_affine_section_value [IsDomain R]
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hab : a*b ≠ 0)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))
    (ell : nativeGradedModuleAwayDegreeZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) 2 (a*b)) :
    let Aij := HomogeneousLocalization.Away 𝒜 (a*b)
    let Bij := HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))
    let F := actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := Aij) (B := Bij)
    let G := nativeNormalizationGlobalWeightedAffineHomSectionsLinearEquiv 𝒜 𝓑 2 (by decide)
      (a*b) (SetLike.mul_mem_graded ha hb)
    G (nativeDualGlobalHomWeightedOverlapLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj ell) =
      F (nativeNormalizationWeightedOverlapDualLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj ell) := by
  dsimp only
  simp only [nativeDualGlobalHomWeightedOverlapLinearEquiv,
    id_eq, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

end LinearStudy
