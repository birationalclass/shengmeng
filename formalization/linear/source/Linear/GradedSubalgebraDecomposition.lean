module
/-
Homogeneous subalgebra step of the Hilbert--Serre induction.
Reuse mathlib's homogeneous Subsemiring closure theorem instead of
rebuilding the old PR 9819 subgrading machinery.
-/
public import Linear.GradedSubmoduleDecomposition
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]

/-- The actual algebra adjoined by homogeneous generators is homogeneous. -/
theorem homogeneousAdjoin (s : Set A)
    (hs : ∀ a ∈ s, SetLike.IsHomogeneousElem 𝒜 a) :
    (Algebra.adjoin K s).toSubmodule.IsHomogeneous 𝒜 := by
  have h : DirectSum.SetLike.IsHomogeneous 𝒜
      (Subsemiring.closure (Set.range (algebraMap K A) ∪ s)) :=
    IsHomogeneous.subsemiringClosure_of_isHomogeneousElem (𝒜 := 𝒜) (by
      intro a ha
      rcases ha with ⟨c, rfl⟩ | ha
      · refine ⟨0, ?_⟩
        simpa only [Algebra.smul_def, mul_one] using
          (𝒜 0).smul_mem c (SetLike.one_mem_graded 𝒜)
      · exact hs a ha)
  exact h

/-- Actual homogeneous pieces of a subalgebra; no grading is supplied. -/
def gradedSubalgebraPiece (B : Subalgebra K A) (n : ℕ) : Submodule K B :=
  (𝒜 n).comap B.val.toLinearMap

/-- The homogeneous subalgebra's actual multiplication-compatible grading. -/
@[instance_reducible] def gradedSubalgebraGrading (B : Subalgebra K A)
    (hB : B.toSubmodule.IsHomogeneous 𝒜) : GradedAlgebra (gradedSubalgebraPiece 𝒜 B) where
  __ := gradedSubmoduleDecomposition 𝒜 B.toSubmodule hB
  one_mem := SetLike.one_mem_graded 𝒜
  mul_mem := by
    intro n k a b ha hb
    change (a : A) * (b : A) ∈ 𝒜 (n + k)
    change (a : A) ∈ 𝒜 n at ha
    change (b : A) ∈ 𝒜 k at hb
    exact SetLike.mul_mem_graded ha hb

theorem gradedSubalgebraPiece_finite (B : Subalgebra K A) (n : ℕ)
    [Module.Finite K (𝒜 n)] : Module.Finite K (gradedSubalgebraPiece 𝒜 B n) :=
  gradedSubmodulePiece_finite 𝒜 B.toSubmodule n

end LinearStudy
