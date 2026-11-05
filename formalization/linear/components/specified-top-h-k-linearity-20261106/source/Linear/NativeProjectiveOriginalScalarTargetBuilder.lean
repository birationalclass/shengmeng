module
public import Linear.NativeProjectiveOriginalScalarPointwiseActual
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
public import Linear.NativeProjectiveOriginalScalarSourceBuilder
public import Linear.ConcreteAdditiveEquivSquare
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ c : R,c ∈ A n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
  schemeModuleToActualAbelianSheaf
/-- Fix the original actual section objects and scalar endomorphisms
before specializing the additive equivalence or its pointwise proof. -/
def nativeProjectiveOriginalScalarTargetBuilder
    (z : R) (r : Γ(Spec (CommRingCat.of K),⊤))
    (e : nativeProjectiveModuleSections A D hR 0 (op (Proj.basicOpen A z)) ≃+
      nativeProjectiveModuleSections B D hS 0 (op (Proj.basicOpen B (algebraMap R S z)))) :=
  let UB := Proj.basicOpen B (algebraMap R S z)
  let fB := ((schemeModuleToActualAbelianSheaf (Proj B)).map
    (originalGlobalModuleScalar
      ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop r)
      (nativeProjectiveModuleSheaf B D hS 0))).hom
  nativeProjectiveOriginalScalarSourceBuilder A B D hR hS z r e (fB.app (op UB))
end LinearStudy
