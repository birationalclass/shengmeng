module
public import Linear.NativeProjectiveActualCoefficientTargetBuilder
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M N : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module K N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hRD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hSD : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hRE : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (hSE : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
/-- A native coefficient section square is the SAME actual abelian-sheaf
section-morphism square. No finite presentation or torsion assumptions. -/
def nativeProjectiveActualAbelianSectionIso_coefficient
    (U : (Proj A).Opens) (V : (Proj B).Opens)
    (eM : nativeProjectiveModuleSections A D hRD 0 (op U) ≃+
      nativeProjectiveModuleSections B D hSD 0 (op V))
    (eN : nativeProjectiveModuleSections A E hRE 0 (op U) ≃+
      nativeProjectiveModuleSections B E hSE 0 (op V))
    (h : ∀ x,eN (nativeProjectiveDegreeZeroSectionMap A D E hRD hRE (f.restrictScalars R) hf 0 (op U) x) =
      nativeProjectiveDegreeZeroSectionMap B D E hSD hSE f hf 0 (op V) (eM x)) :=
  let fA := ((schemeModuleToActualAbelianSheaf (Proj A)).map
    (nativeProjectiveDegreeZeroSheafMap A D E hRD hRE (f.restrictScalars R) hf 0)).hom
  let fB := ((schemeModuleToActualAbelianSheaf (Proj B)).map
    (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf 0)).hom
  nativeProjectiveActualAbelianSectionIsoCoefficientTargetBuilder A B D E hRD hSD hRE hSE
    U V eM eN (fA.app (op U)) (fB.app (op V)) h
end LinearStudy
