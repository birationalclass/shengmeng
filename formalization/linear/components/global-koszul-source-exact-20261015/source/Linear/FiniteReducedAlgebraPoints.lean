module
public import Linear.PointDecomposition
public import Linear.FiniteRationalPoints
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.LinearAlgebra.Dimension.Constructions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
  [Module.Finite K A]

/-- Each actual maximal residue field is the original algebraically closed
base field. The residue evaluations and their exact kernels are constructed. -/
theorem finiteAlgebra_exists_maximal_residue_evaluations :
    ∃ q : MaximalSpectrum A → A →ₐ[K] K,
      ∀ p, RingHom.ker (q p).toRingHom = p.asIdeal := by
  have he (p : MaximalSpectrum A) : ∃ q : A →ₐ[K] K, RingHom.ker q.toRingHom = p.asIdeal := by
    letI : p.asIdeal.IsMaximal := p.isMaximal
    letI : Field (A ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
    let e : K ≃ₐ[K] (A ⧸ p.asIdeal) := AlgEquiv.ofBijective (Algebra.ofId K _)
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K p.asIdeal), ?_⟩
    ext a
    change e.symm (Ideal.Quotient.mk p.asIdeal a) = 0 ↔ a ∈ p.asIdeal
    rw [map_eq_zero_iff e.symm e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  choose q hq using he
  exact ⟨q, hq⟩

/-- A reduced finite-dimensional algebra is isomorphic to the functions
on its ACTUAL maximal spectrum, without a supplied product decomposition. -/
theorem finiteReducedAlgebra_exists_point_function_equiv [IsReduced A] :
    Nonempty (A ≃ₐ[K] (MaximalSpectrum A → K)) := by
  letI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  obtain ⟨q, hq⟩ := finiteAlgebra_exists_maximal_residue_evaluations (K := K) (A := A)
  let E := maximalResidueEvaluation q
  have hinj : Function.Injective E := by
    apply (RingHom.injective_iff_ker_eq_bot E.toRingHom).mpr
    rw [maximalResidueEvaluation_kernel q hq, nilradical_eq_zero A]
    rfl
  exact ⟨AlgEquiv.ofBijective E ⟨hinj, maximalResidueEvaluation_surjective q hq⟩⟩

theorem finiteReducedAlgebra_finrank_eq_maximal_card [IsReduced A] :
    Module.finrank K A = Nat.card (MaximalSpectrum A) := by
  letI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  obtain ⟨e⟩ := finiteReducedAlgebra_exists_point_function_equiv (K := K) (A := A)
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

theorem scalarAlgHom_eq_of_kernel_eq (φ ψ : A →ₐ[K] K)
    (hk : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom) : φ = ψ := by
  apply AlgHom.ext
  intro a
  have hz : a - algebraMap K A (φ a) ∈ RingHom.ker φ.toRingHom := by
    change φ (a - algebraMap K A (φ a)) = 0
    simp
  rw [hk] at hz
  change ψ (a - algebraMap K A (φ a)) = 0 at hz
  exact (show ψ a = φ a by
    simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_eq_zero] using hz).symm

/-- Actual scalar-valued points are in bijection with the actual maximal
spectrum, using algebraic closedness and finite dimension. -/
theorem finiteAlgebra_nonempty_rationalPoint_maximal_equiv :
    Nonempty ((A →ₐ[K] K) ≃ MaximalSpectrum A) := by
  let j : (A →ₐ[K] K) → MaximalSpectrum A := fun φ =>
    ⟨RingHom.ker φ.toRingHom, RingHom.ker_isMaximal_of_surjective φ.toRingHom (by
      intro k
      exact ⟨algebraMap K A k, by simp⟩)⟩
  have hinj : Function.Injective j := by
    intro φ ψ h
    exact scalarAlgHom_eq_of_kernel_eq φ ψ (congrArg MaximalSpectrum.asIdeal h)
  obtain ⟨q, hq⟩ := finiteAlgebra_exists_maximal_residue_evaluations (K := K) (A := A)
  have hsurj : Function.Surjective j := by
    intro p
    exact ⟨q p, MaximalSpectrum.ext (hq p)⟩
  exact ⟨Equiv.ofBijective j ⟨hinj, hsurj⟩⟩

theorem finiteReducedAlgebra_finrank_eq_rationalPoint_card [IsReduced A] :
    Module.finrank K A = Nat.card (A →ₐ[K] K) := by
  obtain ⟨e⟩ := finiteAlgebra_nonempty_rationalPoint_maximal_equiv (K := K) (A := A)
  rw [finiteReducedAlgebra_finrank_eq_maximal_card (K := K)]
  exact (Nat.card_congr e).symm

end LinearStudy
