module
public import Linear.NativeProjectiveOriginalScalarPointwiseActual
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
public import Linear.NativeProjectiveActualCoefficientTargetBuilder
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
def nativeProjectiveOriginalScalarSourceBuilder
    (z : R) (r : Γ(Spec (CommRingCat.of K),⊤))
    (e : nativeProjectiveModuleSections A D hR 0 (op (Proj.basicOpen A z)) ≃+
      nativeProjectiveModuleSections B D hS 0 (op (Proj.basicOpen B (algebraMap R S z)))) :=
  let UA := Proj.basicOpen A z
  let UB := Proj.basicOpen B (algebraMap R S z)
  let FA := ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hR 0)).obj
  let FB := ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B D hS 0)).obj
  let fA := ((schemeModuleToActualAbelianSheaf (Proj A)).map
    (originalGlobalModuleScalar
      ((Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A 0)))).appTop r)
      (nativeProjectiveModuleSheaf A D hR 0))).hom
  nativeProjectiveActualAbelianSectionIsoCoefficientTargetBuilder A B D D hR hS hR hS
    UA UB e e (fA.app (op UA))
end LinearStudy
