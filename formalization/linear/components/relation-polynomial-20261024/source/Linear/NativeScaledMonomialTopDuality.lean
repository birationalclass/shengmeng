module
public import Linear.NativePolynomialComplexFamily
public import Linear.NativeMonomialTopDualityNaturality
public import Linear.ModuleTopHomologyScalar
public import Linear.ProjectiveHomogeneousMultiplicationFamily
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

theorem coordinateNativeScaledComplementaryMonomialComplex_naturality (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) (κ : K) :
    (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ)).hom ≫
      (((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm κ) •
        coordinateComplementaryMonomialComplexMap (K := K) l m b) =
    coordinateNativeComplementaryPolynomialComplexMap (K := K) l m
      (κ • projectiveHomogeneousMonomialBasis (R := K) l b) ≫
      (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ)
        (-(m:ℤ)-Fintype.card σ)).hom := by
  rw [coordinateComplementaryMonomialComplexMap_eq_shift, ← Linear.smul_comp]
  unfold coordinateNativeComplementaryPolynomialComplexMap
  rw [← coordinatePositiveScaledMonomialPolynomial_eq_basis]
  have h := coordinateNativeScaledMonomialCechComplex_naturality (K := K) l
    (projectiveMonomialPositiveWeight l b) (projectiveMonomialPositiveWeight_nonnegative l b) κ
    (-((l+m:ℕ):ℤ)-Fintype.card σ)
  rw [reassoc_of% h, coordinateNativeLaurentComplexDegreeCast_naturality] <;>
    simp only [Category.assoc]

/-- The outgoing-zero premise of the scalar homology lemma is actually
satisfied by the original coordinate complex in its top degree. -/
theorem coordinateLaurentFullTop_sc_g_zero (d : ℤ) (n : ℕ)
    (hc : Fintype.card σ = n+2) :
    ((coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) d).sc (n+1)).g = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change ((coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) d).d
    (n+1) ((ComplexShape.up ℕ).next (n+1))).hom s = 0
  have hn : (ComplexShape.up ℕ).next (n+1) = (n+1)+1 :=
    (ComplexShape.up ℕ).next_eq' (by rfl)
  rw [hn, coordinateNativeLaurentOrderedCechComplex_d]
  exact coordinateHomogeneousLaurent_top_is_cycle d (n+1) hc s

theorem coordinateLaurentFullTopHomologyDualIso_scaled_monomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l)
    (q : coordinateCanonicalBaseRing K) :
    HomologicalComplex.homologyMap (q • coordinateComplementaryMonomialComplexMap (K := K) l m b) (n+1) ≫
      (coordinateLaurentFullTopHomologyDualIso (K := K) m n hc).hom =
    (coordinateLaurentFullTopHomologyDualIso (K := K) (l+m) n hc).hom ≫
      ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l m
        (q • projectiveHomogeneousMonomialBasis (R := coordinateCanonicalBaseRing K) l b)) := by
  rw [HomologicalComplex.moduleCatTopHomologyMap_scale q _ (n+1)
      (coordinateLaurentFullTop_sc_g_zero _ n hc) (coordinateLaurentFullTop_sc_g_zero _ n hc),
    projectiveHomogeneousMultiplyDual_scaled]
  change (q • HomologicalComplex.homologyMap
      (coordinateComplementaryMonomialComplexMap (K := K) l m b) (n+1)) ≫ _ =
    _ ≫ (q • ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l m
      (projectiveHomogeneousMonomialBasis (R := coordinateCanonicalBaseRing K) l b)))
  rw [Linear.smul_comp, coordinateLaurentFullTopHomologyDualIso_monomial_naturality, Linear.comp_smul]

/-- Arbitrary ORIGINAL monomial coefficients now satisfy actual native
top Cech duality naturality, with the canonical coefficient-ring map explicit. -/
theorem coordinateNativeGeneralTopHomologyDualIso_scaled_monomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l) (κ : K) :
    HomologicalComplex.homologyMap (coordinateNativeComplementaryPolynomialComplexMap (K := K) l m
      (κ • projectiveHomogeneousMonomialBasis (R := K) l b)) (n+1) ≫
      (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) m n hc).hom =
    (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) (l+m) n hc).hom ≫
      ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l m
        (((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm κ) •
          projectiveHomogeneousMonomialBasis (R := coordinateCanonicalBaseRing K) l b)) := by
  rw [coordinateNativeGeneralTopHomologyDualIso_eq_comparison,
    coordinateNativeGeneralTopHomologyDualIso_eq_comparison]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f (n+1))
    (coordinateNativeScaledComplementaryMonomialComplex_naturality (K := K) l m b κ)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  rw [← Category.assoc, ← h, Category.assoc,
    coordinateLaurentFullTopHomologyDualIso_scaled_monomial_naturality, ← Category.assoc]

end MvPolynomial
