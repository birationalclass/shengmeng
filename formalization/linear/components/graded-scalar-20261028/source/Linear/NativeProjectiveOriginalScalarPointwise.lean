module
public import Linear.NativeProjectiveModuleBaseScalarValue
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
/-- Two ORIGINAL actual scalar-map value theorems convert the proved
native scalar square into the ORIGINAL actual pointwise square.
The scalar square remains explicit only in this generic builder. -/
def nativeProjectiveOriginalScalarPointwise
    (z : R) (r : Γ(Spec (CommRingCat.of K),⊤))
    (e : nativeProjectiveModuleSections A D hR 0 (op (Proj.basicOpen A z)) ≃+
      nativeProjectiveModuleSections B D hS 0 (op (Proj.basicOpen B (algebraMap R S z))))
    (hs : ∀ s,e (nativeProjectiveModuleScalarApply A D hR 0 (op (Proj.basicOpen A z))
      (projBasicOpenBaseScalar A (algebraMap K (A 0)) z r) s) =
      nativeProjectiveModuleScalarApply B D hS 0 (op (Proj.basicOpen B (algebraMap R S z)))
        (projBasicOpenBaseScalar B (algebraMap K (B 0)) (algebraMap R S z) r) (e s)) :=
  fun (s : nativeProjectiveModuleSections A D hR 0 (op (Proj.basicOpen A z))) =>
    (congrArg e (nativeProjectiveModuleActualBaseScalar_app A D hR 0 z r s)).trans
      ((hs s).trans (nativeProjectiveModuleActualBaseScalar_app B D hS 0 (algebraMap R S z) r (e s)).symm)
end LinearStudy
