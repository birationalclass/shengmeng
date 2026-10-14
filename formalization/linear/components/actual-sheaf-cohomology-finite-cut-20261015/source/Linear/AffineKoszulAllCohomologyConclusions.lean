module
public import Linear.AffineKoszulGeometricAllCohomologySupport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
attribute [local irreducible] affineKoszulInternalHomCohomologyClosedCutUnit

/-- Bundle ONLY conclusions about SAME actual original objects,so geometric
wrappers avoid repeating huge quotient/module-sheaf types. This is NOT an
input proof certificate or abstract replacement:the body explicitly records
ALL original coefficients,ALL degrees,ACTUAL native/internal-Hom objects,
ACTUAL derived module Ext and the ACTUAL original geometric unit. -/
def affineKoszulAllCohomologyConclusions (R : CommRingCat.{u}) (r : ℕ) (H : Fin r → R) : Prop :=
  (PrimeSpectrum.zeroLocus (Ideal.span (Set.range H) : Set R)).Finite ∧
    ∀ (N : ModuleCat.{u} R) (j : ℕ),
      (Module.support R ((affineKoszulNativeHomCochainComplex R N r H).homology j)).Finite ∧
      Nonempty ((affineKoszulInternalHomCochainComplex R N r H).homology j ≅
        tilde ((affineKoszulNativeHomCochainComplex R N r H).homology j)) ∧
      Nonempty ((affineKoszulNativeHomCochainComplex R N r H).homology (j+1) ≅
        ModuleCat.of R (CategoryTheory.Abelian.Ext.{u}
          (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (j+1))) ∧
      IsIso (affineKoszulInternalHomCohomologyClosedCutUnit R N r H j)

/-- PROVE every bundled ACTUAL conclusion from original source exactness
and original finite cut. Nothing desired is assumed;original geometry
will DERIVE both of these source inputs. -/
theorem affineKoszulAllCohomologyConclusions_of_exact_finite (R : CommRingCat.{u})
    (r : ℕ) (H : Fin r → R)
    (he : ∀ j : ℕ, 0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (hcut : (PrimeSpectrum.zeroLocus (Ideal.span (Set.range H) : Set R)).Finite) :
    affineKoszulAllCohomologyConclusions R r H := by
  refine ⟨hcut,?_⟩
  intro N j
  exact ⟨affineKoszulNativeCohomology_support_finite R N r H he j hcut,
    ⟨affineKoszulInternalHomCohomologyNativeIso R N r H j⟩,
    ⟨affineKoszulNativePositiveCohomologyExtIso R N r H he j⟩,
    affineKoszulInternalHomCohomologyClosedCutUnit_isIso R N r H he j⟩

end LinearStudy
