module
public import Linear.ProjectiveLinearSectionPointEquiv
public import Linear.ProjectiveHomogeneousGenericControl
public import Linear.PolynomialLinearHighestComponents
public import Linear.HomogeneousCoordinateComponentProduct
public import Linear.ProjectiveFilteredReflection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open scoped TensorProduct
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct a homogeneous generic basis and one common denominator
for an actual finite map into a homogeneous coordinate quotient. -/
theorem finite_coordinate_map_exists_generic_homogeneous_control
    {K σ R : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _))
    (φ : R →ₐ[K] (MvPolynomial σ K ⧸ I)) (hfinite : φ.Finite) :
    let A := MvPolynomial σ K ⧸ I
    letI : Algebra R A := φ.toRingHom.toAlgebra
    letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
    letI : Module R A := Algebra.toModule
    ∃ (m : ℕ) (b : Fin m → A) (s : R), m = Module.finrank R A ∧
      (∀ i, ∃ d : ℕ, b i ∈ homogeneousQuotientPiece I d) ∧
      LinearIndependent R b ∧ s ≠ 0 ∧
      ∀ x : A, ∃ c : Fin m → R, (∑ i, φ (c i) * b i) = φ s * x := by
  classical
  let A := MvPolynomial σ K ⧸ I
  let F := FractionRing R
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
  letI : Module R A := Algebra.toModule
  letI : Module.Finite R A := hfinite
  letI := homogeneousQuotientGrading I hI
  let N := F ⊗[R] A
  let l : A →ₗ[R] N := TensorProduct.mk R F A 1
  obtain ⟨m,b,hm,hhom,hli,hspan⟩ :=
    finiteModule_exists_generic_homogeneous_basis (A := R) (homogeneousQuotientPiece I) F l
  have hd : Module.finrank F N = Module.finrank R A :=
    (IsLocalization.finrank_eq F (nonZeroDivisors R) le_rfl).trans
      (IsLocalizedModule.finrank_eq (nonZeroDivisors R) l le_rfl)
  have hliR : LinearIndependent R (fun i => l (b i)) := hli.restrict_scalars' R
  have hb : LinearIndependent R b := hliR.of_comp l
  obtain ⟨s,hs,hden⟩ := finiteModule_genericFamily_exists_common_denominator F l b hspan
  refine ⟨m,b,s,hm.trans hd,hhom,hb,hs,?_⟩
  intro x
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hden x)
  exact ⟨c,hc⟩

theorem polynomial_totalDegree_le_of_components_zero
    {K σ : Type*} [Field K] (H : MvPolynomial σ K) (N : ℕ)
    (hzero : ∀ j > N, MvPolynomial.homogeneousComponent j H = 0) :
    H.totalDegree ≤ N := by
  classical
  apply (MvPolynomial.mem_restrictTotalDegree σ N H).mp
  rw [← MvPolynomial.sum_homogeneousComponent H]
  apply Submodule.sum_mem
  intro j hj
  by_cases hjN : j ≤ N
  · exact (MvPolynomial.mem_restrictTotalDegree σ N _).mpr
      ((MvPolynomial.homogeneousComponent_isHomogeneous j H).totalDegree_le.trans hjN)
  · rw [hzero j (Nat.lt_of_not_ge hjN)]
    exact (MvPolynomial.restrictTotalDegree σ K N).zero_mem

/-- The actual degree-one substitution commutes with every component. -/
theorem linear_projection_homogeneousComponent
    {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _))
    (L : τ → MvPolynomial σ K) (hL : ∀ i, (L i).IsHomogeneous 1)
    (k : ℕ) (H : MvPolynomial τ K) :
    let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
    homogeneousQuotientComponent I hI k (φ H) =
      φ (MvPolynomial.homogeneousComponent k H) := by
  change homogeneousQuotientComponent I hI k
      (Ideal.Quotient.mk I (MvPolynomial.aeval L H)) =
    Ideal.Quotient.mk I (MvPolynomial.aeval L (MvPolynomial.homogeneousComponent k H))
  rw [homogeneousQuotientComponent_mk,
    polynomial_grading_map_homogeneousComponent (MvPolynomial.aeval L)
      (fun d P hP => by simpa only [one_mul] using hP.aeval L hL)]

theorem linear_projection_filtration_mem
    {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _))
    (L : τ → MvPolynomial σ K) (hL : ∀ i, (L i).IsHomogeneous 1)
    (N : ℕ) (H : MvPolynomial τ K) (hH : H.totalDegree ≤ N) :
    ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)) H ∈
      homogeneousQuotientFiltration I N := by
  apply (homogeneousQuotientFiltration_mem_iff_components I hI N _).mpr
  intro k hk
  rw [linear_projection_homogeneousComponent I hI L hL,
    MvPolynomial.homogeneousComponent_eq_zero k H (hH.trans_lt hk),map_zero]

/-- No high-degree cancellation is possible in an independent family
of actual homogeneous source functions for a degree-one projection. -/
theorem linear_projection_combination_coefficients_bounded
    {K σ τ : Type*} [Field K] {m : ℕ}
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _))
    (L : τ → MvPolynomial σ K) (hL : ∀ i, (L i).IsHomogeneous 1)
    (b : Fin m → MvPolynomial σ K ⧸ I) (d : Fin m → ℕ)
    (hb : ∀ i, b i ∈ homogeneousQuotientPiece I (d i))
    (hli : let R := MvPolynomial τ K
      let A := MvPolynomial σ K ⧸ I
      let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
      letI : Algebra R A := φ.toRingHom.toAlgebra
      letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
      letI : Module R A := Algebra.toModule
      LinearIndependent R b)
    (c : Fin m → MvPolynomial τ K) (N : ℕ)
    (hc : (∑ i, ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)) (c i) * b i) ∈
      homogeneousQuotientFiltration I N) :
    ∀ i, (c i).totalDegree ≤ N := by
  classical
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
  letI : Module R A := Algebra.toModule
  intro i
  apply polynomial_totalDegree_le_of_components_zero
  intro j hj
  let k := j + d i
  have hk : N < k := by dsimp [k]; omega
  let cut : Fin m → R := fun a => if d a ≤ k then
    MvPolynomial.homogeneousComponent (k-d a) (c a) else 0
  have hcomp : homogeneousQuotientComponent I hI k (∑ a,φ (c a) * b a) =
      ∑ a,φ (cut a) * b a := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [homogeneousQuotientComponent_mul_homogeneous I hI (d a) k _ _ (hb a)]
    by_cases hd : d a ≤ k
    · simp only [cut,ite_true,hd]
      rw [linear_projection_homogeneousComponent I hI L hL]
    · simp only [cut,hd,ite_false,map_zero,zero_mul]
  have hzero : (∑ a,φ (cut a) * b a) = 0 := by
    rw [←hcomp]
    exact homogeneousQuotientFiltration_component_zero I hI N k hk _ hc
  have heq : (∑ a,cut a • b a) = ∑ a,(0 : R) • b a := by
    change (∑ a,φ (cut a) * b a) = ∑ a,φ 0 * b a
    simpa only [map_zero,zero_mul,Finset.sum_const_zero] using hzero
  have hi := hli.eq_coords_of_eq heq i
  have hdi : d i ≤ k := by dsimp [k]; omega
  simpa only [cut,ite_true,hdi,k,Nat.add_sub_cancel] using hi

end LinearStudy
