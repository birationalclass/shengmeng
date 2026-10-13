module
public import Linear.NativeBaseSourceGlobalSectionLift
public import Linear.NativeBaseSourceHomogeneousSectionTransfer
public import Linear.HomogeneousQuotientBaseGrading
public import Linear.NativeQuotientPolynomialSectionLift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ORIGINAL homogeneous polynomial on the ORIGINAL quotient Proj.
At each original source prime, its value is the SAME class [Q]/1. -/
def quotientProjHomogeneousPolynomialSection
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (N : ℕ) (Q : MvPolynomial.homogeneousSubmodule σ K N) :
    letI := homogeneousQuotientGrading I hI
    Γ(nativeProjectiveModuleSheaf (homogeneousQuotientPiece I)
      (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece I))
      (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece I)) (N : ℤ),⊤) := by
  letI := homogeneousQuotientGrading I hI
  exact nativePositiveHomogeneousGlobalSection (homogeneousQuotientPiece I) N
    ⟨Ideal.Quotient.mk I Q,(homogeneousQuotientPiece_mem_iff I N _).mpr ⟨Q,Q.property,rfl⟩⟩

/-- There is ONE bound before ALL degrees and sections such that every
actual positive twist section on the ORIGINAL integral quotient Proj
comes from an ORIGINAL homogeneous polynomial of exactly its degree.
Primality is the original integrality hypothesis, not an extra normal,
smooth or Cohen--Macaulay assumption. Local comparison, actual overlap,
source-to-base gluing and preservation of [Q]/1 are all proved. -/
theorem homogeneousPrimeQuotient_eventually_actual_polynomial_sections
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) [I.IsPrime] (j : σ) :
    letI := homogeneousQuotientGrading I hI
    ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N → Function.Surjective
      (quotientProjHomogeneousPolynomialSection I hI N) := by
  letI := homogeneousQuotientGrading I hI
  letI := homogeneousQuotientBaseGradedSMul I
  let R := MvPolynomial σ K
  let S := R ⧸ I
  let A := MvPolynomial.homogeneousSubmodule σ K
  let B := homogeneousQuotientPiece I
  let G := nativeProjectiveRingIntegerPiece B
  let hR := homogeneousQuotientIntegerDegreeCompatibility I hI
  let hS := nativeProjectiveRingIntegerPiece_graded B
  letI : DirectSum.Decomposition G := nativeProjectiveRingIntegerDecomposition B
  let a : ULift.{u} σ → R := fun i => MvPolynomial.X i.down
  have ha : ∀ i, a i ∈ A 1 := fun i => MvPolynomial.isHomogeneous_X K i.down
  have hcover : (⊤ : (Proj A).Opens) ≤ ⨆ i, Proj.basicOpen A (a i) :=
    le_of_eq (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := K) (σ := σ)).symm
  have hgen : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤ :=
    homogeneousQuotient_coordinate_adjoin_eq_top I
  obtain ⟨n₀,hn₀⟩ := homogeneousQuotient_eventually_fraction_polynomial_sections I hI j
  refine ⟨n₀,fun N hN s => ?_⟩
  let D := integerGradingShift G (N : ℤ)
  let hDR := integerGradingShift_smul_homogeneous A G hR (N : ℤ)
  let hDS := integerGradingShift_smul_homogeneous B G hS (N : ℤ)
  letI : DirectSum.Decomposition D := integerGradingShiftDecomposition G (N : ℤ)
  let eR := nativeProjectiveTwistRegradingSectionEquiv A G hR (N : ℤ) (op ⊤)
  let eS := nativeProjectiveTwistRegradingSectionEquiv B G hS (N : ℤ) (op ⊤)
  let s₀ := eS.symm s
  obtain ⟨x,t,ht⟩ := nativeBaseSourceGlobalSection_exists_lift A B D hDR hDS a ha hcover hgen s₀
  obtain ⟨Q,hQ⟩ := hn₀ N hN (eR t)
  let ellN : G (N : ℤ) := ⟨Ideal.Quotient.mk I Q,
    homogeneousQuotientMap_integer_degree I (N : ℤ) Q (by
      simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,ite_true,
        Int.toNat_natCast] using Q.property)⟩
  let ell : D 0 := ⟨ellN,by
    simpa only [D,integerGradingShift,zero_add] using ellN.property⟩
  have hgR : eR (nativeProjectiveModuleHomogeneousGlobalSection A D hDR 0 ell) =
      ambientHomogeneousQuotientPolynomialSection I hI N Q := by
    apply Subtype.ext
    rfl
  have htR : t = nativeProjectiveModuleHomogeneousGlobalSection A D hDR 0 ell :=
    eR.injective (hQ.symm.trans hgR.symm)
  have hs₀ := nativeBaseSourceGlobalSection_homogeneous_fraction A B D hDR hDS
    a ha hgen x t s₀ ht ell htR
  have hgS : eS (nativeProjectiveModuleHomogeneousGlobalSection B D hDS 0 ell) =
      quotientProjHomogeneousPolynomialSection I hI N Q := by
    apply Subtype.ext
    rfl
  refine ⟨Q,?_⟩
  exact hgS.symm.trans ((congrArg eS hs₀).symm.trans (eS.apply_symm_apply s))
end LinearStudy
