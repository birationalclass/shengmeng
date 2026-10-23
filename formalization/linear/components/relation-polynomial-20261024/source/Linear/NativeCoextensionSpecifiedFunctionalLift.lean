module
public import Linear.NativeCoextensionSpecifiedTraceAdjointPairing
public import Linear.IntegerGradedHomPieceFinite
public import Linear.FiniteAdditiveDualRepresentative
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [IsDomain S] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  coextensionGradedDecomposition coextensionOriginalBaseScalarTower
attribute [local instance] coextensionTraceBaseSourceTower coextensionTraceFieldSourceTower
  coextensionTraceFiniteBase coextensionTraceFiniteSource coextensionTraceTorsionFree
  schemeModuleActualCohomologyAddCommGroup
attribute [local irreducible] nativeFiniteNormalization_specifiedActualTopHomDualIso
variable {M : Type} [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M] [Module S M]
variable [IsScalarTower (MvPolynomial σ K) S M] [IsScalarTower K (MvPolynomial σ K) M] [IsScalarTower K S M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K n →
  ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable [Module.IsTorsionFree S M] [Module.Finite (MvPolynomial σ K) M] [Module.Finite S M]
attribute [local irreducible] nativeCoextensionSpecifiedTopEvaluationTrace integerGradedHomPrecomposition
  nativeProjectiveModuleSheaf nativeProjectiveDegreeZeroSheafMap
include hR in
/-- ORIGINAL coefficient-scalar linearity is written explicitly,not
transported through the comparison. Every such functional on actual
H(M(-card sigma)) is represented by an ACTUAL coefficient map to the SAME
C(-card sigma),using the CONSTRUCTED model trace and PROVED Hom finiteness.
No canonical omega identification or full Hom-perfectness is asserted. -/
theorem nativeCoextensionSpecifiedTrace_exists_functional_lift_of_originalScalar
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (ell : schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))) (q+1) →+ K)
    (hlinear : ∀ r : K,∀ x,
      ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
        (originalGlobalModuleScalar
          ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r))
          (nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))))) (q+1) x)=r * ell x) :
    ∃ a : nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)) ⟶
        nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
          (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
          (-(Fintype.card σ:ℤ)),
      ∀ x,nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map a)
          (q+1) x)=ell x := by
  let H := schemeModuleActualCohomology (Proj B)
    (nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))) (q+1)
  let V : Type := integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
    (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ)))
  letI : Module.Finite K V := polynomialIntegerGradedHomPiece_finite D _
  let J := nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard
    (-(Fintype.card σ:ℤ))
  let e : H ≃+ Module.Dual K V := actualAbelianIsoAddEquiv (K:=K) (H:=H) (V:=V) J
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let rho : K → H → H := fun r =>
    CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r))
        (nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))))) (q+1)
  have hscalar (r : K) (x : H) : e (rho r x)=r • e x :=
    nativeFiniteNormalization_specifiedActualTopHomDualIso_originalScalar
      B D hR hS c hc hgenC q hcard (-(Fintype.card σ:ℤ)) r x
  have hrep : ∃ psi : V,∀ x : H,e x psi=ell x :=
    finiteAdditiveDual_exists_representative (K:=K) (H:=H) (V:=V) e rho hscalar ell hlinear
  obtain ⟨psi,hpsi⟩ := hrep
  let f := coextensionOriginalAdjoint (S:=S) psi.1
  let hf := coextensionOriginalAdjoint_degreeZero (MvPolynomial.homogeneousSubmodule σ K)
    B D hS (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ))) (sub_self _) psi
  refine ⟨nativeProjectiveDegreeZeroSheafMap B D
    (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) hS
    (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
    f hf (-(Fintype.card σ:ℤ)),?_⟩
  intro x
  have hp := nativeCoextensionSpecifiedTopEvaluationTrace_adjointPairing
    B D hR hS c hc hgenC q hcard psi x
  dsimp only at hp
  exact hp.trans (hpsi x)
end LinearStudy
