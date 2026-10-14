module
public import Linear.ProjectiveComplementaryCechShift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

theorem coordinateLaurentCechDegreeCast_differential {d d' : ℤ} (h : d=d') (n : ℕ) :
    ModuleCat.ofHom (coordinateLaurentCechDegreeCast (R := R) (σ := σ) h n) ≫
      coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d' n =
    coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d n ≫
      ModuleCat.ofHom (coordinateLaurentCechDegreeCast (R := R) (σ := σ) h (n+1)) := by
  cases h
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The explicitly normalized complementary multiplication still commutes
with the actual Cech differential in every cochain degree. -/
theorem coordinateComplementaryMonomialCechShift_differential (l m n : ℕ)
    (b : ProjectiveMonomialIndex σ l) :
    ModuleCat.ofHom (coordinateComplementaryMonomialCechShift (R := R) l m b n) ≫
      coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ)
        (-(m:ℤ)-Fintype.card σ) n =
    coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) n ≫
      ModuleCat.ofHom (coordinateComplementaryMonomialCechShift (R := R) l m b (n+1)) := by
  change (coordinateLaurentCechShift (R := R) (d := -((l+m:ℕ):ℤ)-Fintype.card σ)
      (projectiveMonomialPositiveWeight l b) (projectiveMonomialPositiveWeight_nonnegative l b) n ≫
    ModuleCat.ofHom (coordinateLaurentCechDegreeCast (R := R)
      (projectiveComplementaryShiftDegree (σ := σ) l m) n)) ≫ _ =
    _ ≫ (coordinateLaurentCechShift (R := R) (d := -((l+m:ℕ):ℤ)-Fintype.card σ)
      (projectiveMonomialPositiveWeight l b) (projectiveMonomialPositiveWeight_nonnegative l b) (n+1) ≫
    ModuleCat.ofHom (coordinateLaurentCechDegreeCast (R := R)
      (projectiveComplementaryShiftDegree (σ := σ) l m) (n+1)))
  rw [Category.assoc, coordinateLaurentCechDegreeCast_differential,
    ← Category.assoc, coordinateLaurentCechShift_differential, Category.assoc]

end MvPolynomial
