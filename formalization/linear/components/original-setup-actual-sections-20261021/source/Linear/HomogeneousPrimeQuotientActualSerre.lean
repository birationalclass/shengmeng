module
public import Linear.NativeFiniteGradedSourceAmbientOrderedTwistCech
public import Linear.NativeFiniteGradedCechVanishing
public import Linear.OrderedModuleCechActualAbelian
public import Linear.FiniteTypeNativeProjActualCohomology
public import Linear.NativeProjectiveTwistFinitePresentation
public import Linear.HomogeneousQuotientBaseGrading
public import Linear.NativeHomogeneousQuotientPolynomialLift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Transfer SAME original ambient ordered Cech exactness to positive actual H
on the integral quotient Proj.All comparison,QC,Noetherianity and affine
intersection facts are constructed;the subsequent theorem derives exactness. -/
theorem homogeneousPrimeQuotient_actualHigherH_vanish_of_ambientOrderedExact
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) [I.IsPrime] (N : ℕ) :
    letI := homogeneousQuotientGrading I hI
    let A := MvPolynomial.homogeneousSubmodule σ K
    let B := homogeneousQuotientPiece I
    let G := nativeProjectiveRingIntegerPiece B
    let hR := homogeneousQuotientIntegerDegreeCompatibility I hI
    (∀ q,(Scheme.Modules.orderedBaseCechComplex
      (MvPolynomial.homogeneousProjπ (R := K) (σ := σ)) (nativeProjectiveModuleSheaf A G hR (N : ℤ))
      (MvPolynomial.coordinateOpenCover (R := K) (σ := σ))).ExactAt (q+1)) →
    ∀ q,Subsingleton (schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B G (nativeProjectiveRingIntegerPiece_graded B) (N : ℤ)) (q+1)) := by
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
  have ha : ∀ i,a i ∈ A 1 := fun i => MvPolynomial.isHomogeneous_X K i.down
  have hrange : Set.range a = Set.range (MvPolynomial.X : σ → R) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩;exact ⟨i.down,rfl⟩
    · rintro ⟨i,rfl⟩;exact ⟨ULift.up i,rfl⟩
  have hgenR : Algebra.adjoin K (Set.range a) = ⊤ := by
    rw [hrange]
    exact MvPolynomial.adjoin_range_X
  have hgenS : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤ :=
    homogeneousQuotient_coordinate_adjoin_eq_top I
  let b : ULift.{u} σ → S := fun i => algebraMap R S (a i)
  have hb : ∀ i,b i ∈ B 1 := fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i)
  have hcover : (⨆ i,Proj.basicOpen B (b i)) = ⊤ :=
    degreeOneGenerated_nativeProj_cover B b hb hgenS
  letI : IsLocallyNoetherian (Proj B) := finiteTypeNativeProj_isLocallyNoetherian_of_cover B b hb hcover
  let F := nativeProjectiveModuleSheaf B G hS (N : ℤ)
  letI : F.IsFinitePresentation :=
    nativeFiniteGradedTwist_isFinitePresentation_of_cover B G hS (N : ℤ) b hb hcover
  letI : F.IsQuasicoherent := inferInstance
  change (∀ q,(Scheme.Modules.orderedBaseCechComplex
    (MvPolynomial.homogeneousProjπ (R := K) (σ := σ)) (nativeProjectiveModuleSheaf A G hR (N : ℤ))
      (MvPolynomial.coordinateOpenCover (R := K) (σ := σ))).ExactAt (q+1)) →
    ∀ q,Subsingleton (schemeModuleActualCohomology (Proj B) F (q+1))
  intro hC q
  refine noetherianFiniteOrderedAffineCover_actualHigherH_vanish (Proj B)
    (fun i => Proj.basicOpen B (b i)) (by rw [hcover])
    (fun p t => nativeProjective_cechIntersection_isAffine B b hb p t.1) F ?_ q
  intro p
  let H := forget₂ (ModuleCat.{u} Γ(Spec (CommRingCat.of K),⊤)) AddCommGrpCat.{u}
  have hA : ((H.mapHomologicalComplex (.up ℕ)).obj
      (Scheme.Modules.orderedBaseCechComplex (MvPolynomial.homogeneousProjπ (R := K) (σ := σ))
        (nativeProjectiveModuleSheaf A G hR (N : ℤ)) (MvPolynomial.coordinateOpenCover (R := K) (σ := σ)))).ExactAt (p+1) :=
    ShortComplex.Exact.map (hC p) H
  have hAb := hA.of_iso (orderedModuleCechActualAbelianComplexIso
    (MvPolynomial.homogeneousProjπ (R := K) (σ := σ)) (nativeProjectiveModuleSheaf A G hR (N : ℤ))
      (MvPolynomial.coordinateOpenCover (R := K) (σ := σ)))
  exact hAb.of_iso (nativeFiniteGradedSourceAmbientOrderedTwistCechIso A B G hR hS a ha hgenR hgenS (N : ℤ))
/-- ONE bound before ALL later INTEGER twists and ALL positive ACTUAL sheaf-H
on the ORIGINAL integral homogeneous quotient Proj.No ambient/source-H
substitution,vanishing certificate,CM or smoothness hypothesis is used. -/
theorem homogeneousPrimeQuotient_eventually_allInteger_actualHigherH_vanish
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) [I.IsPrime] (j : σ) :
    letI := homogeneousQuotientGrading I hI
    let B := homogeneousQuotientPiece I
    let G := nativeProjectiveRingIntegerPiece B
    ∃ b : ℕ,∀ k : ℤ,(b : ℤ) ≤ k → ∀ q : ℕ,
      Subsingleton (schemeModuleActualCohomology (Proj B)
        (nativeProjectiveModuleSheaf B G (nativeProjectiveRingIntegerPiece_graded B) k) (q+1)) := by
  letI := homogeneousQuotientGrading I hI
  let B := homogeneousQuotientPiece I
  let G := nativeProjectiveRingIntegerPiece B
  let hR := homogeneousQuotientIntegerDegreeCompatibility I hI
  letI : DirectSum.Decomposition G := nativeProjectiveRingIntegerDecomposition B
  obtain ⟨b,hb⟩ := MvPolynomial.coordinateNativeFiniteGraded_eventually_allPositive_orderedCech_exactAt G hR j
  refine ⟨b,fun k hk q => ?_⟩
  have h0 : 0 ≤ k := le_trans (Int.natCast_nonneg b) hk
  have he : (k.toNat : ℤ)=k := Int.toNat_of_nonneg h0
  have hN : b ≤ k.toNat := by omega
  simpa only [he] using homogeneousPrimeQuotient_actualHigherH_vanish_of_ambientOrderedExact I hI k.toNat (hb k.toNat hN) q
end LinearStudy
