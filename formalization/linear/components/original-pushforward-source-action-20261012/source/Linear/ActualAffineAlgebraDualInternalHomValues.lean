module
public import Linear.ActualAffineAlgebraDualInternalHomLinear
public import Linear.NativeAffineInternalHomLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- The same affine linear comparison retains its actual tilde functional,
actual structure pushforward isomorphism and actual structure-unit map. -/
theorem actualAffineAlgebraDualInternalHomSectionsLinearEquiv_value
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (f : B →ₗ[A] A) :
    let P := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    schemeModuleHomTopSectionsEquiv P Q
      (actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := A) (B := B) f) =
      (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).inv ≫
        (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f) ≫
        (tildeSelf (R := CommRingCat.of A)).hom := by
  rfl

variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  normalizationHomogeneousSourceChartAlgebra

/-- The affine comparison reused on weighted overlaps agrees EXACTLY with
the OLD actual degree-one affine section comparison on original chart elements. -/
theorem actualAffineAlgebraDualInternalHomSectionsLinearEquiv_eq_native
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    (finiteNativeDualFullSourceChartEquiv 𝒜 𝓑 a ha hinj).trans
      (actualAffineAlgebraDualInternalHomSectionsLinearEquiv
        (A := HomogeneousLocalization.Away 𝒜 a)
        (B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a))) =
      nativeAffineInternalHomSectionsLinearEquiv 𝒜 𝓑 a ha hinj := by
  ext ell
  rfl

end LinearStudy
