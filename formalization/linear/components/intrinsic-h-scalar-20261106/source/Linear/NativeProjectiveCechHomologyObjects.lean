module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
public import Linear.OrderedFreeSheafHomCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S M N : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup N] [Module K N] [Module S N]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hE : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable {ι : Type u} [LinearOrder ι]
/-- EXACT original ordered-Cech homology object of the actual native sheaf. -/
def nativeProjectiveOrderedCechHomologyObject (b : ι → S) (k : ℤ) (n : ℕ) : AddCommGrpCat.{u} :=
  (orderedTopAbelianCechComplex (Proj B) (fun i => Proj.basicOpen B (b i))
    ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hD k))).homology n
/-- EXACT original coefficient map on this SAME ordered-Cech homology. -/
def nativeProjectiveOrderedCechHomologyCoefficientHom
    (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
    (b : ι → S) (k : ℤ) (n : ℕ) :
    nativeProjectiveOrderedCechHomologyObject B D hD b k n ⟶
      nativeProjectiveOrderedCechHomologyObject B E hE b k n :=
  HomologicalComplex.homologyMap
    (orderedTopAbelianCechCoefficientMap (Proj B) (fun i => Proj.basicOpen B (b i))
      ((schemeModuleToActualAbelianSheaf (Proj B)).map
        (nativeProjectiveDegreeZeroSheafMap B D E hD hE f hf k))) n
/-- Underlying map is the ACTUAL original homologyMap,definitionally. -/
theorem nativeProjectiveOrderedCechHomologyCoefficientHom_eq_original
    (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
    (b : ι → S) (k : ℤ) (n : ℕ) :
    nativeProjectiveOrderedCechHomologyCoefficientHom B D E hD hE f hf b k n =
      HomologicalComplex.homologyMap
        (orderedTopAbelianCechCoefficientMap (Proj B) (fun i => Proj.basicOpen B (b i))
          ((schemeModuleToActualAbelianSheaf (Proj B)).map
            (nativeProjectiveDegreeZeroSheafMap B D E hD hE f hf k))) n := rfl
end LinearStudy
