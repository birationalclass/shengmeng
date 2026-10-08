module
public import Linear.ProjectivePullbackAllComponents
public import Linear.HomogeneousCoordinateComponentProduct
public import Linear.ProjectiveFilteredReflection
public import Linear.ProjectiveHomogeneousGenericControl
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n m : ℕ}

/-- The degree-k component of an actual pullback-linear combination is
itself a pullback-linear combination of the corresponding coefficient
components. Every divisibility and degree shift is explicit. -/
theorem projectiveCoordinateCombination_component
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (b c : Fin m → CoordinateRing n ⧸ V.ideal.toIdeal) (d : Fin m → ℕ)
    (hb : ∀ i, b i ∈ homogeneousQuotientPiece V.ideal.toIdeal (d i)) (k : ℕ) :
    homogeneousQuotientComponent V.ideal.toIdeal V.ideal.isHomogeneous k
        (∑ i, projectiveCoordinateDomainMap f V hq hf hV (c i) * b i) =
      ∑ i, projectiveCoordinateDomainMap f V hq hf hV
        (if d i ≤ k ∧ f.degree ∣ k - d i then
          homogeneousQuotientComponent V.ideal.toIdeal V.ideal.isHomogeneous
            ((k - d i) / f.degree) (c i) else 0) * b i := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [homogeneousQuotientComponent_mul_homogeneous V.ideal.toIdeal
    V.ideal.isHomogeneous (d i) k _ _ (hb i)]
  by_cases hd : d i ≤ k
  · rw [ite_eq_left hd, projectiveCoordinateDomainMap_component_all f V hq hf hV]
    by_cases hdiv : f.degree ∣ k - d i <;> simp [hd, hdiv]
  · simp [hd]

/-- An actual homogeneous independent family prevents cancellation of
high-degree coefficients: if the combination has degree at most N, each
coefficient has degree at most N/q. Independence is for the ORIGINAL
pullback action, not ordinary multiplication. -/
theorem projectiveCoordinateCombination_coefficients_bounded
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (b c : Fin m → CoordinateRing n ⧸ V.ideal.toIdeal) (d : Fin m → ℕ)
    (hb : ∀ i, b i ∈ homogeneousQuotientPiece V.ideal.toIdeal (d i))
    (hli : let A := CoordinateRing n ⧸ V.ideal.toIdeal
      let φ := projectiveCoordinateDomainMap f V hq hf hV
      letI : Algebra A A := φ.toRingHom.toAlgebra
      letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
      letI : Module A A := Algebra.toModule
      LinearIndependent A b)
    (N : ℕ)
    (hc : (∑ i, projectiveCoordinateDomainMap f V hq hf hV (c i) * b i) ∈
      homogeneousQuotientFiltration V.ideal.toIdeal N) :
    ∀ i, c i ∈ homogeneousQuotientFiltration V.ideal.toIdeal (N / f.degree) := by
  classical
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveCoordinateDomainMap f V hq hf hV
  letI : Algebra A A := φ.toRingHom.toAlgebra
  letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
  letI : Module A A := Algebra.toModule
  intro i
  apply (homogeneousQuotientFiltration_mem_iff_components
    V.ideal.toIdeal V.ideal.isHomogeneous (N / f.degree) (c i)).mpr
  intro j hj
  let k := f.degree * j + d i
  have hmul : N < f.degree * j := by
    simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hq).mp hj
  have hk : N < k := by dsimp [k]; omega
  let cut : Fin m → A := fun a => if d a ≤ k ∧ f.degree ∣ k - d a then
    homogeneousQuotientComponent V.ideal.toIdeal V.ideal.isHomogeneous
      ((k - d a) / f.degree) (c a) else 0
  have hzero : (∑ a, φ (cut a) * b a) = 0 := by
    rw [← projectiveCoordinateCombination_component f V hq hf hV b c d hb k]
    exact homogeneousQuotientFiltration_component_zero V.ideal.toIdeal
      V.ideal.isHomogeneous N k hk _ hc
  have heq : (∑ a, cut a • b a) = ∑ a, (0 : A) • b a := by
    change (∑ a, φ (cut a) * b a) = ∑ a, φ 0 * b a
    simpa only [map_zero, zero_mul, Finset.sum_const_zero] using hzero
  have hi : cut i = 0 := hli.eq_coords_of_eq heq i
  have hdi : d i ≤ k := by dsimp [k]; omega
  have hdiv : f.degree ∣ k - d i := by simp [k]
  simpa only [cut, ite_eq_left (And.intro hdi hdiv), k, Nat.add_sub_cancel,
    Nat.mul_div_cancel_left j hq] using hi

end LinearStudy
