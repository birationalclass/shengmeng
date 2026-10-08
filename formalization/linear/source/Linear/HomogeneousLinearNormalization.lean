/-
The integral induction follows mathlib NoetherNormalization, Apache 2.0,
Copyright (c) 2025 Sihan Su; authors Riccardo Brasca, Sihan Su, Wan Lin,
Xiaoyang Su. Degree-one coordinate changes and homogeneous-kernel proofs
are supplied here: the ordinary nonlinear Nagata changes do not suffice.
-/
module
public import Linear.HomogeneousLinearElimination
public import Linear.NoetherNormalizationKrull
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] {n : ℕ}

/-- The kernel of the actual linear elimination is homogeneous. This
is needed for iteration; merely assuming the next kernel is homogeneous
would not construct linear Noether normalization. -/
theorem homogeneous_linear_elimination_kernel
    (a : Fin n → K) (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _)) :
    (RingHom.ker (polynomialLinearEliminationHom
      (homogeneousCoordinateShearEquiv a) I)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule _ _) := by
  let E := homogeneousCoordinateShearEquiv a
  let T : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n+1)) K :=
    E.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ)
  have hT (d : ℕ) (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous d) :
      (T P).IsHomogeneous d :=
    homogeneousCoordinateShear_isHomogeneous (-a) _ hP.rename_isHomogeneous
  intro j P hP
  change (MvPolynomial.decomposition.decompose' P j : MvPolynomial (Fin n) K) ∈ _ 
  rw [MvPolynomial.decomposition.decompose'_apply]
  change polynomialLinearEliminationHom E I (MvPolynomial.homogeneousComponent j P) = 0
  change polynomialLinearEliminationHom E I P = 0 at hP
  rw [polynomialLinearEliminationHom_formula] at hP ⊢
  have hp : T P ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hP
  have hc := MvPolynomial.homogeneousComponent_mem_of_mem hI hp j
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change T (MvPolynomial.homogeneousComponent j P) ∈ I
  rw [← polynomial_grading_map_homogeneousComponent T hT]
  exact hc

/-- A nonzero element of a homogeneous ideal supplies a nonzero actual
homogeneous equation, obtained from its finite homogeneous decomposition. -/
theorem homogeneous_ideal_nonzero_equation
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _)) (hne : I ≠ ⊥) :
    ∃ d : ℕ, ∃ H : MvPolynomial (Fin n) K, H ∈ I ∧ H ≠ 0 ∧ H.IsHomogeneous d := by
  classical
  obtain ⟨P,hP,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hh : ∃ d, MvPolynomial.homogeneousComponent d P ≠ 0 := by
    by_contra! h
    apply hne
    rw [← MvPolynomial.sum_homogeneousComponent P]
    simp [h]
  obtain ⟨d,hd⟩ := hh
  exact ⟨d,_,MvPolynomial.homogeneousComponent_mem_of_mem hI hP d,hd,
    MvPolynomial.homogeneousComponent_isHomogeneous d P⟩

/-- Genuine linear Noether normalization for a proper homogeneous ideal
over an infinite field. Every generator is represented by an actual
degree-one homogeneous original polynomial, not a nonlinear Nagata form.
The homomorphism, injectivity and integrality are all constructed. -/
theorem exists_linear_integral_normalization [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hi : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _)) :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I),
      Function.Injective g ∧ g.IsIntegral ∧
        ∀ i : Fin s, ∃ L : MvPolynomial (Fin n) K,
          L.IsHomogeneous 1 ∧ g (MvPolynomial.X i) = Ideal.Quotient.mk I L := by
  classical
  induction n with
  | zero =>
    obtain ⟨s,hs,g,hinj,hint⟩ := exists_integral_inj_algHom_of_quotient I hi
    have hs0 : s = 0 := Nat.eq_zero_of_le_zero hs
    subst s
    exact ⟨0,le_rfl,g,hinj,hint,fun i => Fin.elim0 i⟩
  | succ m ih =>
    by_cases hz : I = ⊥
    · have hbij : Function.Bijective (Ideal.Quotient.mkₐ K I) :=
        (Ideal.Quotient.mk_bijective_iff_eq_bot I).mpr hz
      refine ⟨m+1,le_rfl,Ideal.Quotient.mkₐ K I,hbij.1,
        RingHom.isIntegral_of_surjective _ hbij.2,?_⟩
      intro i
      exact ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X _ _,rfl⟩
    · obtain ⟨d,H,hmem,hne,hH⟩ := homogeneous_ideal_nonzero_equation I hI hz
      obtain ⟨a,ha,hlin⟩ := homogeneous_exists_linear_integral_elimination I H hH hne hmem
      let g0 := polynomialLinearEliminationHom (homogeneousCoordinateShearEquiv a) I
      let J := RingHom.ker g0
      letI : Nontrivial (MvPolynomial (Fin (m+1)) K ⧸ I) :=
        Ideal.Quotient.nontrivial_iff.mpr hi
      have hJ : J ≠ ⊤ := RingHom.ker_ne_top g0
      obtain ⟨s,hsm,g,hinj,hint,hlinear⟩ :=
        ih J hJ (homogeneous_linear_elimination_kernel a I hI)
      let φ := Ideal.kerLiftAlg g0
      refine ⟨s,by omega,φ.comp g,(φ.coe_comp g) ▸
        (Ideal.kerLiftAlg_injective _).comp hinj,
        hint.trans g.toRingHom φ.toRingHom ha.kerLift,?_⟩
      intro i
      obtain ⟨L,hL,hg⟩ := hlinear i
      refine ⟨(homogeneousCoordinateShearEquiv a).symm (MvPolynomial.rename Fin.succ L),
        homogeneousCoordinateShear_isHomogeneous (-a) _ hL.rename_isHomogeneous,?_⟩
      rw [AlgHom.comp_apply,hg]
      change g0 L = _
      exact polynomialLinearEliminationHom_formula _ I L

/-- The constructed linear normalization is genuinely module-finite,
and the number of its variables equals the actual Krull dimension.
Neither finiteness nor a numerical dimension is assumed as an input. -/
theorem exists_linear_finite_normalization_krull_dimension [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hi : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _)) :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I),
      Function.Injective g ∧ g.Finite ∧
        ringKrullDim (MvPolynomial (Fin n) K ⧸ I) = (s : WithBot ℕ∞) ∧
        ∀ i : Fin s, ∃ L : MvPolynomial (Fin n) K,
          L.IsHomogeneous 1 ∧ g (MvPolynomial.X i) = Ideal.Quotient.mk I L := by
  obtain ⟨s,hs,g,hinj,hint,hlinear⟩ := exists_linear_integral_normalization I hi hI
  letI : Nontrivial (MvPolynomial (Fin n) K ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hi
  have hc : algebraMap K (MvPolynomial (Fin n) K ⧸ I) =
      g.toRingHom.comp (algebraMap K (MvPolynomial (Fin s) K)) :=
    RingHom.ext fun x => (g.commutes x).symm
  have hfg : Algebra.FiniteType K (MvPolynomial (Fin n) K ⧸ I) := inferInstance
  have hfinite : g.Finite := hint.to_finite
    (hc ▸ RingHom.finiteType_algebraMap.mpr hfg).of_comp_finiteType
  letI : Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    g.toRingHom.toAlgebra
  letI : Module.Finite (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    RingHom.finite_algebraMap.mp hfinite
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    inferInstance
  have hdim := integral_injective_ringKrullDim_eq
    (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) hinj
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field,Nat.card_fin,zero_add] at hdim
  exact ⟨s,hs,g,hinj,hfinite,hdim.symm,hlinear⟩

end LinearStudy
