module
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.GradedAlgebra.Noetherian
public import Mathlib.RingTheory.FiniteType
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]

/-- The actual homogeneous affine chart is Noetherian for a finite-type
graded algebra. No chart Noetherian hypothesis is added: grade zero
is Noetherian, and the original finite-type algebra gives the actual
degree-zero localization finite type by mathlib's graded theorem. -/
theorem finiteTypeHomogeneousChart_isNoetherian
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    (a : A) (d : ℕ) (ha : a ∈ 𝒜 d) :
    IsNoetherianRing (HomogeneousLocalization.Away 𝒜 a) := by
  letI : IsScalarTower K (𝒜 0) A :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := 𝒜 0) (A := A) (fun _ => rfl)
  letI : Algebra.FiniteType (𝒜 0) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (𝒜 0) A
  letI : Algebra.FiniteType (𝒜 0) (HomogeneousLocalization.Away 𝒜 a) :=
    HomogeneousLocalization.Away.finiteType a d ha
  exact Algebra.FiniteType.isNoetherianRing (𝒜 0) (HomogeneousLocalization.Away 𝒜 a)
end LinearStudy
