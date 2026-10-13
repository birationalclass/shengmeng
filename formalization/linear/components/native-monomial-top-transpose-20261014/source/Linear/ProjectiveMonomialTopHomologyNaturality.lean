module
public import Linear.ProjectiveMonomialTopQuotientNaturality
public import Linear.ProjectiveComplementaryCechDifferential
public import Linear.ModuleShortComplexTopQuotientNaturality
public import Linear.NativeProjectiveGeneralTopDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- The original Laurent multiplication gives an actual short-complex
morphism after the proved complementary-degree normalization. -/
def coordinateComplementaryMonomialShortComplexMap (l m n : ℕ)
    (b : ProjectiveMonomialIndex σ l) :
    coordinateLaurentGeneralShortComplex (K := K) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) n ⟶
    coordinateLaurentGeneralShortComplex (K := K) (σ := σ)
      (-(m:ℤ)-Fintype.card σ) n where
  τ₁ := ModuleCat.ofHom (coordinateComplementaryMonomialCechShift l m b n)
  τ₂ := ModuleCat.ofHom (coordinateComplementaryMonomialCechShift l m b (n+1))
  τ₃ := ModuleCat.ofHom (coordinateComplementaryMonomialCechShift l m b (n+2))
  comm₁₂ := coordinateComplementaryMonomialCechShift_differential l m n b
  comm₂₃ := coordinateComplementaryMonomialCechShift_differential l m (n+1) b

theorem coordinateComplementaryMonomialShortComplexMap_quotient (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l) :
    ShortComplex.moduleCatBoundaryQuotientMap
      (coordinateComplementaryMonomialShortComplexMap (K := K) l m n b) =
    coordinateComplementaryMonomialTopQuotientMap (R := K) l m n hc b := rfl

theorem coordinateGeneralTopQuotientDualIso_monomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l) :
    ModuleCat.ofHom (coordinateComplementaryMonomialTopQuotientMap (R := K) l m n hc b) ≫
      (coordinateGeneralTopQuotientDualEquiv (R := K) m n hc).toModuleIso.hom =
    (coordinateGeneralTopQuotientDualEquiv (R := K) (l+m) n hc).toModuleIso.hom ≫
      ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l m
        (projectiveHomogeneousMonomialBasis (R := coordinateCanonicalBaseRing K) l b)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact coordinateGeneralTopQuotientDualEquiv_monomial_naturality l m n hc b s

/-- The actual short-complex homology map is transpose to actual
homogeneous polynomial multiplication under the previously verified duality.
No homology map is defined by transport through that duality. -/
theorem coordinateLaurentGeneralHomologyDualIso_monomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l) :
    ShortComplex.homologyMap (coordinateComplementaryMonomialShortComplexMap (K := K) l m n b) ≫
      (coordinateLaurentGeneralHomologyDualIso (K := K) m n hc).hom =
    (coordinateLaurentGeneralHomologyDualIso (K := K) (l+m) n hc).hom ≫
      ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l m
        (projectiveHomogeneousMonomialBasis (R := coordinateCanonicalBaseRing K) l b)) := by
  have h := ShortComplex.moduleCatTopHomologyQuotient_naturality
    (coordinateComplementaryMonomialShortComplexMap (K := K) l m n b)
    (coordinateLaurentGeneralShortComplex_g_eq_zero _ n hc)
    (coordinateLaurentGeneralShortComplex_g_eq_zero _ n hc)
  rw [coordinateComplementaryMonomialShortComplexMap_quotient l m n hc b] at h
  change ShortComplex.homologyMap (coordinateComplementaryMonomialShortComplexMap (K := K) l m n b) ≫
      ((coordinateLaurentGeneralShortComplex (K := K) (σ := σ) _ n).asIsoHomologyι
        (coordinateLaurentGeneralShortComplex_g_eq_zero _ n hc) ≪≫
        (coordinateLaurentGeneralShortComplex (K := K) (σ := σ) _ n).moduleCatOpcyclesIso).hom ≫
      (coordinateGeneralTopQuotientDualEquiv (R := K) m n hc).toModuleIso.hom =
    (((coordinateLaurentGeneralShortComplex (K := K) (σ := σ) _ n).asIsoHomologyι
        (coordinateLaurentGeneralShortComplex_g_eq_zero _ n hc) ≪≫
        (coordinateLaurentGeneralShortComplex (K := K) (σ := σ) _ n).moduleCatOpcyclesIso).hom ≫
      (coordinateGeneralTopQuotientDualEquiv (R := K) (l+m) n hc).toModuleIso.hom) ≫ _
  rw [← Category.assoc, h, Category.assoc,
    coordinateGeneralTopQuotientDualIso_monomial_naturality, ← Category.assoc]

end MvPolynomial
