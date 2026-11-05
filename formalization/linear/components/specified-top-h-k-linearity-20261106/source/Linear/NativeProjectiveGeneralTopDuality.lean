module
public import Linear.ProjectiveGeneralResidueDuality
public import Linear.NativeProjectiveLaurentComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} {σ : Type} [Field K] [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateLaurentGeneralShortComplex (d : ℤ) (n : ℕ) :
    ShortComplex (ModuleCat (coordinateCanonicalBaseRing K)) :=
  ShortComplex.mk
    (coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) d n)
    (coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) d (n+1))
    (coordinateNativeLaurentOrderedCechDifferential_comp d n)

theorem coordinateLaurentGeneralShortComplex_g_eq_zero (d : ℤ) (n : ℕ)
    (hc : Fintype.card σ = n+2) :
    (coordinateLaurentGeneralShortComplex (K := K) (σ := σ) d n).g = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact coordinateHomogeneousLaurent_top_is_cycle d (n+1) hc s

def coordinateLaurentGeneralHomologyDualIso (m n : ℕ) (hc : Fintype.card σ = n+2) :
    (coordinateLaurentGeneralShortComplex (K := K) (σ := σ)
      (-(m : ℤ)-Fintype.card σ) n).homology ≅
      ModuleCat.of (coordinateCanonicalBaseRing K)
        (Module.Dual (coordinateCanonicalBaseRing K)
          (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) m)) :=
  (coordinateLaurentGeneralShortComplex (K := K) (σ := σ) _ n).asIsoHomologyι
      (coordinateLaurentGeneralShortComplex_g_eq_zero _ n hc) ≪≫
    (coordinateLaurentGeneralShortComplex (K := K) (σ := σ) _ n).moduleCatOpcyclesIso ≪≫
      (coordinateGeneralTopQuotientDualEquiv (R := K) m n hc).toModuleIso

def coordinateLaurentGeneralShortComplexIso (d : ℤ) (n : ℕ) :
    (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) d).sc' n (n+1) (n+2) ≅
      coordinateLaurentGeneralShortComplex (K := K) (σ := σ) d n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 _ ≫ coordinateHomogeneousLaurentOrderedCechDifferential d n =
        (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) d).d n (n+1) ≫ 𝟙 _
      simp)
    (by
      change 𝟙 _ ≫ coordinateHomogeneousLaurentOrderedCechDifferential d (n+1) =
        (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) d).d (n+1) (n+2) ≫ 𝟙 _
      simp)

/-- Actual native coordinate Cech top homology in degree -m-r-1 is dual
to actual homogeneous degree-m polynomials, for every m>=0 and r>=1.
This is a Cech computation, not a derived proper-duality comparison. -/
def coordinateNativeGeneralTopHomologyDualIso (m n : ℕ) (hc : Fintype.card σ = n+2) :
    (Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(m : ℤ)-Fintype.card σ))
      (coordinateOpenCover (R := K) (σ := σ))).homology (n+1) ≅
      ModuleCat.of (coordinateCanonicalBaseRing K)
        (Module.Dual (coordinateCanonicalBaseRing K)
          (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) m)) :=
  HomologicalComplex.homologyMapIso
      (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ)
        (-(m : ℤ)-Fintype.card σ)) (n+1) ≪≫
    (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ)
      (-(m : ℤ)-Fintype.card σ)).homologyIsoSc' n (n+1) (n+2) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (coordinateLaurentGeneralShortComplexIso _ n) ≪≫
      coordinateLaurentGeneralHomologyDualIso m n hc
end MvPolynomial
