module
public import Linear.CoordinateCechCoefficientForgettingIdentity
public import Linear.SpecifiedDualityCoefficientTransfer
public import Linear.NativeSpecifiedNormalizationActualTopDuality
public import Linear.NativeIndependentNormalizationModuleHCoefficient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S M N : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M] [Module S M]
variable [IsScalarTower (MvPolynomial σ K) S M] [IsScalarTower K (MvPolynomial σ K) M] [IsScalarTower K S M]
variable [AddCommGroup N] [Module K N] [Module (MvPolynomial σ K) N] [Module S N]
variable [IsScalarTower (MvPolynomial σ K) S N] [IsScalarTower K (MvPolynomial σ K) N] [IsScalarTower K S N]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (E : ℤ → Submodule K N) [DirectSum.Decomposition E]
variable (hRM : ∀ t : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K t → ∀ x : M,x ∈ D j → z • x ∈ D ((t:ℤ)+j))
variable (hSM : ∀ t : ℕ,∀ j : ℤ,∀ z : S,z ∈ B t → ∀ x : M,x ∈ D j → z • x ∈ D ((t:ℤ)+j))
variable (hRN : ∀ t : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K t → ∀ x : N,x ∈ E j → z • x ∈ E ((t:ℤ)+j))
variable (hSN : ∀ t : ℕ,∀ j : ℤ,∀ z : S,z ∈ B t → ∀ x : N,x ∈ E j → z • x ∈ E ((t:ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M] [Module.IsTorsionFree S N]
variable [IsNoetherianRing S] [Algebra.FiniteType K S] [Module.Finite (MvPolynomial σ K) S]
variable [Module.Finite (MvPolynomial σ K) M] [Module.Finite S M]
variable [Module.Finite (MvPolynomial σ K) N] [Module.Finite S N]
/-- The SAME originally specified actual-top comparison is natural for the
ORIGINAL S-linear degree-zero coefficient map,all integer twists and
positive top degree q+1 with card sigma=q+2. No omega/trace identification
is asserted or assumed by this statement. -/
theorem nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficient
    (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ) :
    (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map
      ((schemeModuleToActualAbelianSheaf (Proj B)).map
        (nativeProjectiveDegreeZeroSheafMap B D E hSM hSN f hf k)) ≫
      (nativeFiniteNormalization_specifiedActualTopHomDualIso B E hRN hSN c hc hgenC q hcard k).hom =
    (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hRM hSM c hc hgenC q hcard k).hom ≫
      (forget₂ (ModuleCat K) AddCommGrpCat).map
        (ModuleCat.ofHom (integerGradedHomPrecomposition (MvPolynomial.homogeneousSubmodule σ K)
          D E (f.restrictScalars (MvPolynomial σ K)) hf (-(Fintype.card σ:ℤ)-k)).dualMap) := by
  let A := MvPolynomial.homogeneousSubmodule σ K
  let a : ULift.{0} σ → MvPolynomial σ K := fun i => MvPolynomial.X i.down
  have ha : ∀ i,a i ∈ A 1 := fun i => MvPolynomial.isHomogeneous_X K i.down
  have hgenA : Algebra.adjoin K (Set.range a) = ⊤ := by
    have hrange : Set.range a = Set.range (MvPolynomial.X : σ → MvPolynomial σ K) := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩;exact ⟨i.down,rfl⟩
      · rintro ⟨i,rfl⟩;exact ⟨ULift.up i,rfl⟩
    rw [hrange]
    exact MvPolynomial.adjoin_range_X
  let piA := MvPolynomial.homogeneousProjπ (R:=K) (σ:=σ)
  let G := forget₂ (ModuleCat Γ(Spec (.of K),⊤)) AddCommGrpCat
  let F := forget₂ (ModuleCat K) AddCommGrpCat
  let eM := nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hRM hSM a ha c hc piA hgenA hgenC k q
  let eN := nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B E hRN hSN a ha c hc piA hgenA hgenC k q
  let jM := F.mapIso (MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso D hRM q hcard k)
  let jN := F.mapIso (MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso E hRN q hcard k)
  let alpha := G.map (HomologicalComplex.homologyMap
    (orderedBaseCechActualCoefficientMap piA
      (nativeProjectiveDegreeZeroSheafMap A D E hRM hRN (f.restrictScalars (MvPolynomial σ K)) hf k)
      (fun i => Proj.basicOpen A (a i))) (q+1))
  let h := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map
    ((schemeModuleToActualAbelianSheaf (Proj B)).map (nativeProjectiveDegreeZeroSheafMap B D E hSM hSN f hf k))
  let delta := F.map (ModuleCat.ofHom (integerGradedHomPrecomposition A D E
    (f.restrictScalars (MvPolynomial σ K)) hf (-(Fintype.card σ:ℤ)-k)).dualMap)
  have h1 : alpha ≫ eN.hom = eM.hom ≫ h :=
    nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_coefficient
      A B D E hRM hSM hRN hSN f hf a ha c hc piA hgenA hgenC k q
  have h2 : alpha ≫ jN.hom = jM.hom ≫ delta := by
    have hd := MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso_naturality
      D E hRM hRN (f.restrictScalars (MvPolynomial σ K)) hf q hcard k
    have hh := congrArg (fun z => F.map z) hd
    simp only [Functor.map_comp] at hh
    have hmap : F.map
        ((ModuleCat.restrictScalars (MvPolynomial.coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
          ((MvPolynomial.coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) q).map
            (nativeProjectiveDegreeZeroSheafMap A D E hRM hRN
              (f.restrictScalars (MvPolynomial σ K)) hf k))) = alpha :=
      MvPolynomial.coordinateNativeCechHomologyFunctor_map_forget
        (nativeProjectiveDegreeZeroSheafMap A D E hRM hRN
          (f.restrictScalars (MvPolynomial σ K)) hf k) q
    rw [hmap] at hh
    exact hh
  change h ≫ (eN.symm ≪≫ jN).hom = (eM.symm ≪≫ jM).hom ≫ delta
  exact originalSpecifiedDualityCoefficientSquare_of_comparisonSquares eM eN jM jN alpha h delta h1 h2
end LinearStudy
