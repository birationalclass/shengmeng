module
public import Linear.NativeIntegerMixedPresentationCechHomDuality
public import Linear.NativeIntegerTwistedPresentationQuotientEpi
public import Linear.NativeIntegerFreeRelationMatrixDuality
public import Linear.IntegerShiftedFreeHomogeneousMapLift
public import Linear.IntegerHomEvaluationMapLiftSquare
public import Linear.NativeGradedPresentationMapLiftSquare
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K M N : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
variable [AddCommGroup N] [Module K N] [Module (MvPolynomial σ K) N]
variable [IsScalarTower K (MvPolynomial σ K) N]
variable {IM JM IN JN : Type}
variable [Fintype IM] [DecidableEq IM] [Fintype JM] [DecidableEq JM]
variable [Fintype IN] [DecidableEq IN] [Fintype JN] [DecidableEq JN]
variable (zM : IM → ℤ) (wM : JM → ℤ) (zN : IN → ℤ) (wN : JN → ℤ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (E : ℤ → Submodule K N) [DirectSum.Decomposition E]
variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (hE : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
  ∀ x : N, x ∈ E d → p • x ∈ E ((t:ℤ)+d))
variable (cM : (IM → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (JM → MvPolynomial σ K))
variable (βM : (JM → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
variable (cN : (IN → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (JN → MvPolynomial σ K))
variable (βN : (JN → MvPolynomial σ K) →ₗ[MvPolynomial σ K] N)
variable (hcM : ∀ d : ℤ, ∀ x : IM → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) zM d →
  cM x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) wM d)
variable (hβM : ∀ d : ℤ, ∀ x : JM → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) wM d → βM x ∈ D d)
variable (hcN : ∀ d : ℤ, ∀ x : IN → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) zN d →
  cN x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) wN d)
variable (hβN : ∀ d : ℤ, ∀ x : JN → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) wN d → βN x ∈ E d)
variable (hontoM : Function.Surjective βM) (hexM : LinearMap.range cM=LinearMap.ker βM)
variable (hontoN : Function.Surjective βN) (hexN : LinearMap.range cN=LinearMap.ker βN)
variable (e : M →ₗ[MvPolynomial σ K] N)
variable (he : ∀ d : ℤ, ∀ x : M, x ∈ D d → e x ∈ E d)
variable (n : ℕ) (hcard : Fintype.card σ=n+2)

/-- The ORIGINAL UNTWiSTED constructed mixed-presentation comparison
is natural for EVERY original degree-zero M->N map. The lift tau is
CONSTRUCTED internally. This base comparison theorem is used on D[k]
and E[k+delta] for original homogeneous maps;no comparison is assumed. -/
theorem coordinateNativeIntegerPresentationMap_duality :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          D E hD hE e he 0)) ≫
      (coordinateNativeIntegerPresentationGradedHomDualIso
        zN wN E hE cN βN hcN hβN hontoN hexN n hcard).hom =
    (coordinateNativeIntegerPresentationGradedHomDualIso
      zM wM D hD cM βM hcM hβM hontoM hexM n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerGradedHomPrecomposition (homogeneousSubmodule σ K)
        D E e he (-(Fintype.card σ:ℤ))).dualMap := by
  let B := homogeneousSubmodule σ K
  let G := (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n) ⋙
    ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let d := -(Fintype.card σ:ℤ)
  let qM := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B wM) D
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B wM) hD βM hβM 0
  let qN := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B wN) E
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B wN) hE βN hβN 0
  let f := LinearStudy.nativeProjectiveDegreeZeroSheafMap B D E hD hE e he 0
  let ΦM := coordinateNativeIntegerPresentationGradedHomDualIso
    zM wM D hD cM βM hcM hβM hontoM hexM n hcard
  let ΦN := coordinateNativeIntegerPresentationGradedHomDualIso
    zN wN E hE cN βN hcN hβN hontoN hexN n hcard
  let ΦFM := coordinateNativeIntegerFreeFamilyCoefficientDualIso (K := K) (σ := σ) wM n hcard
  let ΦFN := coordinateNativeIntegerFreeFamilyCoefficientDualIso (K := K) (σ := σ) wN n hcard
  let αM := LinearStudy.integerGradedHomEvaluationCoordinates B wM D βM hβM d
  let αN := LinearStudy.integerGradedHomEvaluationCoordinates B wN E βN hβN d
  let P := LinearStudy.integerGradedHomPrecomposition B D E e he d
  obtain ⟨τ,hτ,hsquare⟩ := LinearStudy.integerShiftedFree_exists_homogeneous_lift B wM wN E
    (e.comp βM) βN (fun t x hx => he t (βM x) (hβM t x hx)) hβN hontoN
  let t := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B wM) (LinearStudy.integerShiftedFreePiece B wN)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B wM)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B wN) τ hτ 0
  let δ := LinearStudy.integerShiftedFreeDualDegreeRelationMatrix τ B wM wN hτ d
  have hs : qM ≫ f=t ≫ qN :=
    LinearStudy.nativeGradedPresentationMapLiftSquare B wM wN D E hD hE βM βN hβM hβN
      e he τ hτ hsquare 0
  have hc : αM.comp P=δ.comp αN :=
    LinearStudy.integerHomEvaluationCoordinates_map_lift B wM wN D E βM βN hβM hβN
      e he τ hτ hsquare d
  have hdual : ModuleCat.ofHom δ.dualMap ≫ ModuleCat.ofHom αN.dualMap =
      ModuleCat.ofHom αM.dualMap ≫ ModuleCat.ofHom P.dualMap := by
    apply ModuleCat.hom_ext
    change αN.dualMap.comp δ.dualMap=P.dualMap.comp αM.dualMap
    rw [LinearMap.dualMap_comp_dualMap,LinearMap.dualMap_comp_dualMap,hc]
  have hQM := coordinateNativeIntegerPresentationGradedHomDualIso_quotient
    zM wM D hD cM βM hcM hβM hontoM hexM n hcard
  rw [LinearStudy.integerPresentationHomCoefficientMap_eq_evaluation] at hQM
  change G.map qM ≫ ΦM.hom=ΦFM.hom ≫ ModuleCat.ofHom αM.dualMap at hQM
  have hQN := coordinateNativeIntegerPresentationGradedHomDualIso_quotient
    zN wN E hE cN βN hcN hβN hontoN hexN n hcard
  rw [LinearStudy.integerPresentationHomCoefficientMap_eq_evaluation] at hQN
  change G.map qN ≫ ΦN.hom=ΦFN.hom ≫ ModuleCat.ofHom αN.dualMap at hQN
  have hF := coordinateNativeIntegerFreeRelation_duality wM wN τ hτ n hcard
  change G.map t ≫ ΦFN.hom=ΦFM.hom ≫ ModuleCat.ofHom δ.dualMap at hF
  haveI : Epi (G.map qM) := coordinateNativeIntegerTwistedPresentationQuotient_epi
    zM wM D hD cM βM hcM hβM hontoM hexM n hcard 0
  change G.map f ≫ ΦN.hom=ΦM.hom ≫ ModuleCat.ofHom P.dualMap
  apply (cancel_epi (G.map qM)).mp
  calc
    G.map qM ≫ (G.map f ≫ ΦN.hom) = G.map t ≫ (G.map qN ≫ ΦN.hom) := by
      rw [← Category.assoc,← G.map_comp,hs,G.map_comp]
      simp only [Category.assoc]
    _ = G.map t ≫ (ΦFN.hom ≫ ModuleCat.ofHom αN.dualMap) := by rw [hQN]
    _ = ΦFM.hom ≫ (ModuleCat.ofHom δ.dualMap ≫ ModuleCat.ofHom αN.dualMap) := by
      rw [← Category.assoc,hF]
      simp only [Category.assoc]
    _ = ΦFM.hom ≫ (ModuleCat.ofHom αM.dualMap ≫ ModuleCat.ofHom P.dualMap) := by rw [hdual]
    _ = G.map qM ≫ (ΦM.hom ≫ ModuleCat.ofHom P.dualMap) := by
      rw [← Category.assoc,← hQM]
      simp only [Category.assoc]

end MvPolynomial
