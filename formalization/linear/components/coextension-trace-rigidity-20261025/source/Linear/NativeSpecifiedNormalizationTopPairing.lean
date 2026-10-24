module
public import Linear.NativeSpecifiedNormalizationTopDualityScalar
public import Linear.ActualAdditiveDualPairing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M] [Module S M]
variable [IsScalarTower (MvPolynomial σ K) S M] [IsScalarTower K (MvPolynomial σ K) M] [IsScalarTower K S M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ d : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K d →
  ∀ x : M,x ∈ D j → z • x ∈ D ((d : ℤ)+j))
variable (hS : ∀ d : ℕ,∀ j : ℤ,∀ z : S,z ∈ B d → ∀ x : M,x ∈ D j → z • x ∈ D ((d : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S] [Module.Finite (MvPolynomial σ K) M] [Module.Finite S M]
attribute [local irreducible] nativeFiniteNormalization_specifiedActualTopHomDualIso
/-- The SAME specified pairing is bilinear for ORIGINAL native-H
coefficient multiplication and ORIGINAL graded-Hom scalars. -/
theorem nativeFiniteNormalization_specifiedActualTopHomDualIso_scalarPairing
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ) (r t : K)
    (x : schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1))
    (phi : integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k)) :
    let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
    (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
      (-(Fintype.card σ:ℤ)-k)) from
      (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k).hom
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
          (originalGlobalModuleScalar (piB.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r))
            (nativeProjectiveModuleSheaf B D hS k))) (q+1) x)) (t • phi) =
      (r*t) * (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
        (-(Fintype.card σ:ℤ)-k)) from
        (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k).hom x) phi := by
  let V := integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k)
  let J := nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let f : Module.Dual K V := J.hom (CategoryTheory.Sheaf.H.map
    ((schemeModuleToActualAbelianSheaf (Proj B)).map (originalGlobalModuleScalar
      (piB.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r))
      (nativeProjectiveModuleSheaf B D hS k))) (q+1) x)
  let g : Module.Dual K V := J.hom x
  have h : f = r • g := nativeFiniteNormalization_specifiedActualTopHomDualIso_originalScalar
    B D hR hS c hc hgenC q hcard k r x
  change f (t • phi) = (r*t) * g phi
  calc
    f (t • phi) = t * f phi := f.map_smul t phi
    _ = t * (r * g phi) := congrArg (fun z : K => t*z) (congrArg (fun ell : Module.Dual K V => ell phi) h)
    _ = (r*t) * g phi := by rw [← mul_assoc,mul_comm t r]
section Nondegeneracy
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
/-- The SAME specified evaluation is left nondegenerate. -/
theorem nativeFiniteNormalization_specifiedActualTopHomDualIso_left_nondegenerate
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ)
    (x : schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1))
    (hz : ∀ phi,(show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K)
      D (-(Fintype.card σ:ℤ)-k)) from
      (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k).hom x) phi=0) : x=0 := by
  let e := actualAbelianIsoAddEquiv (K:=K) (H:=schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1)) (V:=integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k)) (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k)
  apply additiveDualComparisonPairing_left_nondegenerate (K:=K) (H:=schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1)) (V:=integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k)) e x
  intro z
  exact hz z
/-- The SAME specified evaluation is right nondegenerate by ordinary
field dual separation. No finite-dimensionality or geometric trace is asserted. -/
theorem nativeFiniteNormalization_specifiedActualTopHomDualIso_right_nondegenerate
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ)
    (phi : integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k))
    (hz : ∀ x,(show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K)
      D (-(Fintype.card σ:ℤ)-k)) from
      (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k).hom x) phi=0) : phi=0 := by
  let e := actualAbelianIsoAddEquiv (K:=K) (H:=schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1)) (V:=integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k)) (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k)
  apply additiveDualComparisonPairing_right_nondegenerate (K:=K) (H:=schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1)) (V:=integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k)) e phi
  intro z
  exact hz z
end Nondegeneracy
end LinearStudy
