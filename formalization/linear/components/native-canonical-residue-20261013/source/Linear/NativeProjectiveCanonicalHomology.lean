module
public import Linear.NativeProjectiveCanonicalResidue
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} {σ : Type} [Field K] [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The quotient of actual native top cochains by actual boundaries. -/
def coordinateNativeCanonicalCokernelEquiv (n : ℕ) (hc : Fintype.card σ = n+2) :
    (coordinateNativeCanonicalCechTerm (K := K) (σ := σ) (n+1) ⧸
      LinearMap.range (coordinateNativeCanonicalCechDifferential (K := K) (σ := σ) n).hom)
      ≃ₗ[coordinateCanonicalBaseRing K] coordinateCanonicalBaseRing K :=
  (Submodule.quotEquivOfEq _ _ (coordinateNativeCanonicalResidue_ker_eq_range n hc).symm).trans
    ((coordinateNativeCanonicalResidue (K := K) (n+1) hc).quotKerEquivOfSurjective
      (coordinateNativeCanonicalResidue_surjective (n+1) hc))

theorem coordinateNativeCanonicalCokernelEquiv_apply_mk (n : ℕ)
    (hc : Fintype.card σ = n+2)
    (s : coordinateNativeCanonicalCechTerm (K := K) (σ := σ) (n+1)) :
    coordinateNativeCanonicalCokernelEquiv (K := K) n hc (Submodule.Quotient.mk s) =
      coordinateNativeCanonicalResidue (K := K) (n+1) hc s := by
  simp [coordinateNativeCanonicalCokernelEquiv]

theorem coordinateNativeCanonicalCechDifferential_top_eq_zero (n : ℕ)
    (hc : Fintype.card σ = n+2) :
    coordinateNativeCanonicalCechDifferential (K := K) (σ := σ) (n+1) = 0 := by
  apply (Scheme.Modules.orderedBaseCechObject_isZero_of_card_le
    (homogeneousProjπ (R := K) (σ := σ))
    (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(Fintype.card σ : ℤ)))
    (coordinateOpenCover (R := K) (σ := σ)) (n+2) (by simpa using hc.le)).eq_of_tgt

/-- The three actual consecutive native Cech terms. -/
def coordinateNativeCanonicalShortComplex (n : ℕ) :
    ShortComplex (ModuleCat (coordinateCanonicalBaseRing K)) :=
  ShortComplex.mk (coordinateNativeCanonicalCechDifferential (K := K) (σ := σ) n)
    (coordinateNativeCanonicalCechDifferential (K := K) (σ := σ) (n+1))
    (Scheme.Modules.orderedBaseCechDifferential_comp _ _ _ n)

/-- The actual native canonical-twist Cech homology in positive top degree
is the coefficient ring, by the constructed residue. This is not a
comparison with derived sheaf cohomology or proper duality. -/
def coordinateNativeCanonicalHomologyIso (n : ℕ) (hc : Fintype.card σ = n+2) :
    (coordinateNativeCanonicalShortComplex (K := K) (σ := σ) n).homology ≅
      ModuleCat.of (coordinateCanonicalBaseRing K) (coordinateCanonicalBaseRing K) :=
  (coordinateNativeCanonicalShortComplex (K := K) (σ := σ) n).asIsoHomologyι
      (coordinateNativeCanonicalCechDifferential_top_eq_zero n hc) ≪≫
    (coordinateNativeCanonicalShortComplex (K := K) (σ := σ) n).moduleCatOpcyclesIso ≪≫
      (coordinateNativeCanonicalCokernelEquiv (K := K) n hc).toModuleIso

/-- The actual full native Cech complex, with its mathlib homology. -/
abbrev coordinateNativeCanonicalComplex :=
  Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
    (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(Fintype.card σ : ℤ)))
    (coordinateOpenCover (R := K) (σ := σ))

/-- Identification of the concrete adjacent terms with the native complex. -/
def coordinateNativeCanonicalShortComplexIso (n : ℕ) :
    (coordinateNativeCanonicalComplex (K := K) (σ := σ)).sc' n (n+1) (n+2) ≅
      coordinateNativeCanonicalShortComplex (K := K) (σ := σ) n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 _ ≫ coordinateNativeCanonicalCechDifferential n =
        (coordinateNativeCanonicalComplex (K := K) (σ := σ)).d n (n+1) ≫ 𝟙 _
      simp [coordinateNativeCanonicalComplex, coordinateNativeCanonicalCechDifferential])
    (by
      change 𝟙 _ ≫ coordinateNativeCanonicalCechDifferential (n+1) =
        (coordinateNativeCanonicalComplex (K := K) (σ := σ)).d (n+1) (n+2) ≫ 𝟙 _
      simp [coordinateNativeCanonicalComplex, coordinateNativeCanonicalCechDifferential])

/-- Top homology of the actual full native coordinate Cech complex is one
copy of the base ring, with no supplied exactness or residue hypothesis. -/
def coordinateNativeCanonicalComplexHomologyIso (n : ℕ)
    (hc : Fintype.card σ = n+2) :
    (coordinateNativeCanonicalComplex (K := K) (σ := σ)).homology (n+1) ≅
      ModuleCat.of (coordinateCanonicalBaseRing K) (coordinateCanonicalBaseRing K) :=
  (coordinateNativeCanonicalComplex (K := K) (σ := σ)).homologyIsoSc'
      n (n+1) (n+2) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (coordinateNativeCanonicalShortComplexIso n) ≪≫
      coordinateNativeCanonicalHomologyIso n hc
end MvPolynomial
