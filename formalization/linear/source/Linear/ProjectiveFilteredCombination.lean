module
public import Linear.ProjectiveHomogeneousCoefficientBound
public import Mathlib.LinearAlgebra.Dimension.Constructions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n m : ℕ}

/-- The actual K-linear pullback combination of bounded-degree coefficient
functions. It uses the original coordinate pullback, not a supplied matrix. -/
def projectiveFilteredCombination
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (b : Fin m → CoordinateRing n ⧸ V.ideal.toIdeal) (N : ℕ) :
    (Fin m → homogeneousQuotientFiltration V.ideal.toIdeal N) →ₗ[ℂ]
      CoordinateRing n ⧸ V.ideal.toIdeal where
  toFun c := ∑ i, projectiveCoordinateDomainMap f V hq hf hV (c i) * b i
  map_add' c e := by simp [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [map_smul, smul_mul_assoc, Finset.smul_sum]

theorem projectiveFilteredCombination_degree_bound
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (b : Fin m → CoordinateRing n ⧸ V.ideal.toIdeal) (N B : ℕ)
    (hb : ∀ i, b i ∈ homogeneousQuotientFiltration V.ideal.toIdeal B)
    (c : Fin m → homogeneousQuotientFiltration V.ideal.toIdeal N) :
    projectiveFilteredCombination f V hq hf hV b N c ∈
      homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N + B) := by
  change (∑ i, projectiveCoordinateDomainMap f V hq hf hV (c i) * b i) ∈ _
  apply Submodule.sum_mem
  intro i hi
  exact homogeneousQuotientFiltration_mul_mem V.ideal.toIdeal _ _ _ _
    (projectiveCoordinateDomainMap_filtration_mem f V hq hf hV N (c i) (c i).property)
    (hb i)

theorem projectiveFilteredCombination_injective
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (b : Fin m → CoordinateRing n ⧸ V.ideal.toIdeal)
    (hli : let A := CoordinateRing n ⧸ V.ideal.toIdeal
      let φ := projectiveCoordinateDomainMap f V hq hf hV
      letI : Algebra A A := φ.toRingHom.toAlgebra
      letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
      letI : Module A A := Algebra.toModule
      LinearIndependent A b) (N : ℕ) :
    Function.Injective (projectiveFilteredCombination f V hq hf hV b N) := by
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveCoordinateDomainMap f V hq hf hV
  letI : Algebra A A := φ.toRingHom.toAlgebra
  letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
  letI : Module A A := Algebra.toModule
  intro c e heq
  have heq' : (∑ i, (c i : A) • b i) = ∑ i, (e i : A) • b i := heq
  funext i
  exact Subtype.ext (hli.eq_coords_of_eq heq' i)

/-- A genuine lower growth comparison retaining the generic family size.
Its hypotheses can be discharged by the constructed homogeneous basis. -/
theorem projectiveFilteredCombination_finrank_lower
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (b : Fin m → CoordinateRing n ⧸ V.ideal.toIdeal)
    (hli : let A := CoordinateRing n ⧸ V.ideal.toIdeal
      let φ := projectiveCoordinateDomainMap f V hq hf hV
      letI : Algebra A A := φ.toRingHom.toAlgebra
      letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
      letI : Module A A := Algebra.toModule
      LinearIndependent A b) (N B : ℕ)
    (hb : ∀ i, b i ∈ homogeneousQuotientFiltration V.ideal.toIdeal B) :
    m * Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) ≤
      Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N + B)) := by
  letI := homogeneousQuotientFiltration_finite V.ideal.toIdeal N
  letI := homogeneousQuotientFiltration_finite V.ideal.toIdeal (f.degree * N + B)
  let L := (projectiveFilteredCombination f V hq hf hV b N).codRestrict
    (homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N + B))
    (projectiveFilteredCombination_degree_bound f V hq hf hV b N B hb)
  have hL : Function.Injective L := by
    intro c e heq
    exact projectiveFilteredCombination_injective f V hq hf hV b hli N
      (congrArg Subtype.val heq)
  have h := LinearMap.finrank_le_finrank_of_injective hL
  simpa [Module.finrank_pi_fintype] using h

end LinearStudy
