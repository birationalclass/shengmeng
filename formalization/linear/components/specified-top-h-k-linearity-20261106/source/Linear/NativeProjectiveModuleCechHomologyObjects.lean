module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Linear.NativeProjectiveCechHomologyObjects
public import Linear.OrderedModuleCechActualAbelianHomology
public import Linear.OrderedFreeSheafHomCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
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
open AlgebraicGeometry.Scheme.Modules CategoryTheory.Limits
attribute [local irreducible] nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
  schemeModuleToActualAbelianSheaf orderedBaseCechComplex orderedBaseCechActualCoefficientMap
  orderedTopAbelianCechComplex orderedTopAbelianCechCoefficientMap
  orderedModuleCechActualAbelianHomologyIso orderedModuleCechActualAbelianComplexIso
  HomologicalComplex.homologyFunctor
/-- Exact original module-valued Cech homology after its original scalar forgetting. -/
def nativeProjectiveOrderedModuleCechHomologyObject {Y : Scheme.{u}} (pi : Proj B ⟶ Y)
    (b : ι → S) (k : ℤ) (n : ℕ) : AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} Γ(Y,⊤)) AddCommGrpCat.{u}).obj
    ((orderedBaseCechComplex pi (nativeProjectiveModuleSheaf B D hD k)
      (fun i => Proj.basicOpen B (b i))).homology n)
/-- The SAME original module Cech coefficient map,with exact objects cached. -/
def nativeProjectiveOrderedModuleCechHomologyCoefficientHom {Y : Scheme.{u}} (pi : Proj B ⟶ Y)
    (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
    (b : ι → S) (k : ℤ) (n : ℕ) :
    nativeProjectiveOrderedModuleCechHomologyObject B D hD pi b k n ⟶
      nativeProjectiveOrderedModuleCechHomologyObject B E hE pi b k n :=
  (forget₂ (ModuleCat.{u} Γ(Y,⊤)) AddCommGrpCat.{u}).map
    (HomologicalComplex.homologyMap
      (orderedBaseCechActualCoefficientMap pi (nativeProjectiveDegreeZeroSheafMap B D E hD hE f hf k)
        (fun i => Proj.basicOpen B (b i))) n)
/-- The SAME previously proved forgetting comparison,with its exact Cech object named. -/
def nativeProjectiveOrderedModuleCechHomologyIso {Y : Scheme.{u}} (pi : Proj B ⟶ Y)
    (b : ι → S) (k : ℤ) (n : ℕ) :
    nativeProjectiveOrderedModuleCechHomologyObject B D hD pi b k n ≅
      nativeProjectiveOrderedCechHomologyObject B D hD b k n :=
  orderedModuleCechActualAbelianHomologyIso pi (nativeProjectiveModuleSheaf B D hD k)
    (fun i => Proj.basicOpen B (b i)) n
/-- Original coefficient naturality of this SAME forgetting iso. -/
theorem nativeProjectiveOrderedModuleCechHomologyIso_coefficient {Y : Scheme.{u}} (pi : Proj B ⟶ Y)
    (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
    (b : ι → S) (k : ℤ) (n : ℕ) :
    nativeProjectiveOrderedModuleCechHomologyCoefficientHom B D E hD hE pi f hf b k n ≫
      (nativeProjectiveOrderedModuleCechHomologyIso B E hE pi b k n).hom =
    (nativeProjectiveOrderedModuleCechHomologyIso B D hD pi b k n).hom ≫
      nativeProjectiveOrderedCechHomologyCoefficientHom B D E hD hE f hf b k n :=
  orderedModuleCechActualAbelianHomologyIso_coefficient_naturality pi
    (nativeProjectiveDegreeZeroSheafMap B D E hD hE f hf k) (fun i => Proj.basicOpen B (b i)) n
end LinearStudy
