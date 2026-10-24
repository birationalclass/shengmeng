module
public import Linear.NativeSpecifiedNormalizationTopDualityKForget
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
  nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso
  nativeFiniteNormalization_moduleCechActualHigherHKLinearIso
/-- The SAME old specified duality intertwines ORIGINAL native-H
coefficient multiplication by r with actual multiplication by r on the
graded-Hom dual. No scalar action is transported through the comparison. -/
theorem nativeFiniteNormalization_specifiedActualTopHomDualIso_originalScalar
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ)
    (r : K) (x : schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B D hS k) (q+1)) :
    let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
    (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
      (-(Fintype.card σ:ℤ)-k)) from
      (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k).hom
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
          (originalGlobalModuleScalar (piB.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r))
            (nativeProjectiveModuleSheaf B D hS k))) (q+1) x)) =
      r • (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
        (-(Fintype.card σ:ℤ)-k)) from
        (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k).hom x) := by
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let MB := nativeProjectiveModuleSheaf B D hS k
  let V := integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k)
  let I := nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso B D hR hS c hc hgenC q hcard k
  let J := nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k
  have he := congrArg Iso.hom (nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_forget
    B D hR hS c hc hgenC q hcard k)
  have hfun (y : schemeModuleActualCohomology (Proj B) MB (q+1)) :
      (show Module.Dual K V from I.hom y) = (show Module.Dual K V from J.hom y) :=
    ConcreteCategory.congr_hom he y
  have hs := I.hom.hom.map_smul r x
  change (show Module.Dual K V from I.hom
    (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r)) MB))
        (q+1) x)) = r • (show Module.Dual K V from I.hom x) at hs
  exact (hfun _).symm.trans (hs.trans (congrArg (fun z : Module.Dual K V => r • z) (hfun x)))
end LinearStudy
