module
public import Linear.HomogeneousCoordinateGrading
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Actual degree-one generators over K give a cover of the native Proj;
the chart cover is deduced from generation, not assumed as sheaf data. -/
theorem degreeOneGenerated_nativeProj_cover {ι : Type u} (a : ι → S)
    (ha : ∀ i, a i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range a) = ⊤) :
    (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤ := by
  let : IsScalarTower K (𝓑 0) S := ⟨fun c b x => by
    change (c • (b : S)) * x = c • ((b : S) * x)
    exact smul_mul_assoc c (b : S) x⟩
  apply Proj.iSup_basicOpen_eq_top' 𝓑 a (fun i => ⟨1, ha i⟩)
  have hle : Algebra.adjoin K (Set.range a) ≤
      (Algebra.adjoin (𝓑 0) (Set.range a)).restrictScalars K :=
    Algebra.adjoin_le (fun _ hx => Algebra.subset_adjoin hx)
  apply top_le_iff.mp
  intro x _
  exact hle (by rw [hgen]; trivial)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate degree-one opens cover the ORIGINAL homogeneous
coordinate quotient with its constructed native grading. -/
theorem homogeneousQuotient_native_coordinate_chart_cover {σ : Type u}
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    letI := homogeneousQuotientGrading I hI
    (⨆ i : σ, Proj.basicOpen (homogeneousQuotientPiece I)
      (Ideal.Quotient.mk I (MvPolynomial.X i))) = ⊤ := by
  let := homogeneousQuotientGrading I hI
  let q := Ideal.Quotient.mkₐ K I
  apply degreeOneGenerated_nativeProj_cover (homogeneousQuotientPiece I)
    (fun i => q (MvPolynomial.X i))
    (fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i, rfl⟩)
  calc
    Algebra.adjoin K (Set.range (fun i : σ => q (MvPolynomial.X i))) =
        Algebra.adjoin K (q '' Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
      congr 1
      exact Set.range_comp q MvPolynomial.X
    _ = (Algebra.adjoin K (Set.range (MvPolynomial.X : σ → MvPolynomial σ K))).map q :=
      (q.map_adjoin _).symm
    _ = q.range := by rw [MvPolynomial.adjoin_range_X, Algebra.map_top]
    _ = ⊤ := (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective K I)

end LinearStudy
