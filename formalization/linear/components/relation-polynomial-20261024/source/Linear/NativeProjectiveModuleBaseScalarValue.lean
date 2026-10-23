module
public import Linear.NativeProjectiveModuleSheaf
public import Linear.NativeProjectiveModuleScalarApply
public import Linear.ProjBasicOpenBaseScalar
public import Linear.SchemeModuleActualAbelianScalarValue
public import Mathlib.Topology.Sheaves.Forget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D)
variable (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))

attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] originalGlobalModuleScalar
/-- At EVERY integer twist, the ORIGINAL actual abelian-sheaf scalar
coefficient map is exactly the original native module action by the
actual structure-map scalar restricted to the ORIGINAL basic open. -/
theorem nativeProjectiveModuleActualBaseScalar_app (k : ℤ) (a : S)
    (r : Γ(Spec (CommRingCat.of K),⊤))
    (s : nativeProjectiveModuleSections 𝓑 𝒟 hgrade k (op (Proj.basicOpen 𝓑 a))) :
    (((schemeModuleToActualAbelianSheaf (Proj 𝓑)).map
      (originalGlobalModuleScalar
        ((Proj.toSpecZero 𝓑 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝓑 0)))).appTop r)
        (nativeProjectiveModuleSheaf 𝓑 𝒟 hgrade k))).hom.app (op (Proj.basicOpen 𝓑 a))) s =
    nativeProjectiveModuleScalarApply 𝓑 𝒟 hgrade k (op (Proj.basicOpen 𝓑 a))
      (projBasicOpenBaseScalar 𝓑 (algebraMap K (𝓑 0)) a r) s :=
  schemeModuleActualAbelianScalar_app
    ((Proj.toSpecZero 𝓑 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝓑 0)))).appTop r)
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hgrade k) (Proj.basicOpen 𝓑 a) s
end LinearStudy
