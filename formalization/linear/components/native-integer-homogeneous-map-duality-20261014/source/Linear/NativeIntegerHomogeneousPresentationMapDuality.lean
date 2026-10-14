module
public import Linear.NativeIntegerBasePresentationMapDuality
public import Linear.NativeIntegerTwistedPresentationCechHomDuality
public import Linear.IntegerHomogeneousMapTwoTwistDuality
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
variable (δ : ℤ) (e : M →ₗ[MvPolynomial σ K] N)
variable (he : ∀ d : ℤ, ∀ x : M, x ∈ D d → e x ∈ E (d+δ))
variable (n : ℕ) (hcard : Fintype.card σ=n+2)

/-- For EVERY ORIGINAL homogeneous degree-delta map e:M->N and EVERY
integer k,the SAME ORIGINAL constructed native Cech/Hom comparisons
at M(k) and N(k+delta) commute. Regrade BOTH ORIGINAL modules and their
SAME original presentations,apply proved BASE comparison naturality,
and prove original prime-localized and Hom-value transport squares.
No desired comparison,map lift,Koszul square or finite-dimension premise.
This is ordered Cech,not the derived SHEAF/proper-duality identification. -/
theorem coordinateNativeIntegerHomogeneousPresentationMap_duality (k : ℤ) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeProjectiveModuleSheafMap (homogeneousSubmodule σ K)
          D E hD hE δ e he k)) ≫
      (coordinateNativeIntegerTwistedPresentationGradedHomDualIso
        zN wN E hE cN βN hcN hβN hontoN hexN n hcard (k+δ)).hom =
    (coordinateNativeIntegerTwistedPresentationGradedHomDualIso
      zM wM D hD cM βM hcM hβM hontoM hexM n hcard k).hom ≫
      ModuleCat.ofHom (LinearStudy.integerGradedHomBetweenTwistsPrecomposition
        (homogeneousSubmodule σ K) D E δ e he (-(Fintype.card σ:ℤ)) k).dualMap := by
  let B := homogeneousSubmodule σ K
  let G := (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n) ⋙
    ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let d := -(Fintype.card σ:ℤ)
  let Dk := LinearStudy.integerGradingShift D k
  let Ekδ := LinearStudy.integerGradingShift E (k+δ)
  let hDk := LinearStudy.integerGradingShift_smul_homogeneous B D hD k
  let hEkδ := LinearStudy.integerGradingShift_smul_homogeneous B E hE (k+δ)
  letI : DirectSum.Decomposition Dk := LinearStudy.integerGradingShiftDecomposition D k
  letI : DirectSum.Decomposition Ekδ := LinearStudy.integerGradingShiftDecomposition E (k+δ)
  let zMk := fun i => zM i-k
  let wMk := fun j => wM j-k
  let zNkδ := fun i => zN i-(k+δ)
  let wNkδ := fun j => wN j-(k+δ)
  let hcMk := LinearStudy.integerShiftedFreeRelation_regrade B zM wM cM hcM k
  let hβMk := LinearStudy.integerShiftedFreeQuotient_regrade B wM D βM hβM k
  let hcNkδ := LinearStudy.integerShiftedFreeRelation_regrade B zN wN cN hcN (k+δ)
  let hβNkδ := LinearStudy.integerShiftedFreeQuotient_regrade B wN E βN hβN (k+δ)
  let he0 := LinearStudy.integerHomogeneousMap_two_regradings D E δ e he k
  let f0 := LinearStudy.nativeProjectiveDegreeZeroSheafMap B Dk Ekδ hDk hEkδ e he0 0
  let f := LinearStudy.nativeProjectiveModuleSheafMap B D E hD hE δ e he k
  let ΨD := coordinateNativeIntegerPresentationGradedHomDualIso
    zMk wMk Dk hDk cM βM hcMk hβMk hontoM hexM n hcard
  let ΨE := coordinateNativeIntegerPresentationGradedHomDualIso
    zNkδ wNkδ Ekδ hEkδ cN βN hcNkδ hβNkδ hontoN hexN n hcard
  let ιD := LinearStudy.nativeProjectiveTwistRegradingIso B D hD k
  let ιE := LinearStudy.nativeProjectiveTwistRegradingIso B E hE (k+δ)
  let RD := LinearStudy.integerGradedHomRegradingEquiv B D k d
  let RE := LinearStudy.integerGradedHomRegradingEquiv B E (k+δ) d
  let εD := RD.dualMap.toModuleIso
  let εE := RE.dualMap.toModuleIso
  let P0 := LinearStudy.integerGradedHomPrecomposition B Dk Ekδ e he0 d
  let P := LinearStudy.integerGradedHomBetweenTwistsPrecomposition B D E δ e he d k
  have h0 := coordinateNativeIntegerPresentationMap_duality
    zMk wMk zNkδ wNkδ Dk Ekδ hDk hEkδ cM βM cN βN hcMk hβMk hcNkδ hβNkδ
    hontoM hexM hontoN hexN e he0 n hcard
  change G.map f0 ≫ ΨE.hom=ΨD.hom ≫ ModuleCat.ofHom P0.dualMap at h0
  have hprimal : ιD.inv ≫ f0 ≫ ιE.hom=f :=
    LinearStudy.nativeProjectiveHomogeneousMap_two_regradings B D E δ e he hD hE k
  have hfactor : G.map f ≫ G.map ιE.inv=G.map ιD.inv ≫ G.map f0 := by
    have hh : f ≫ ιE.inv=ιD.inv ≫ f0 := by
      rw [← hprimal]
      simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    rw [← G.map_comp,hh,G.map_comp]
  have hpre : RD.toLinearMap.comp P0=P.comp RE.toLinearMap :=
    LinearStudy.integerGradedHomBetweenTwistsPrecomposition_regrade B D E δ e he d k
  have hdual0 : εD.hom ≫ ModuleCat.ofHom P0.dualMap=
      ModuleCat.ofHom P.dualMap ≫ εE.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro eta
    apply LinearMap.ext
    intro φ
    change eta (RD (P0 φ))=eta (P (RE φ))
    exact congrArg eta (LinearMap.congr_fun hpre φ)
  have hdual : ModuleCat.ofHom P0.dualMap ≫ εE.inv=
      εD.inv ≫ ModuleCat.ofHom P.dualMap := by
    apply (cancel_mono εE.hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [← hdual0,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  change G.map f ≫ (G.map ιE.inv ≫ ΨE.hom ≫ εE.inv)=
    (G.map ιD.inv ≫ ΨD.hom ≫ εD.inv) ≫ ModuleCat.ofHom P.dualMap
  calc
    G.map f ≫ (G.map ιE.inv ≫ ΨE.hom ≫ εE.inv) =
        (G.map f ≫ G.map ιE.inv) ≫ ΨE.hom ≫ εE.inv := by simp only [Category.assoc]
    _ = (G.map ιD.inv ≫ G.map f0) ≫ ΨE.hom ≫ εE.inv := by rw [hfactor]
    _ = G.map ιD.inv ≫ (G.map f0 ≫ ΨE.hom) ≫ εE.inv := by simp only [Category.assoc]
    _ = G.map ιD.inv ≫ (ΨD.hom ≫ ModuleCat.ofHom P0.dualMap) ≫ εE.inv := by rw [h0]
    _ = G.map ιD.inv ≫ ΨD.hom ≫ (ModuleCat.ofHom P0.dualMap ≫ εE.inv) := by
      simp only [Category.assoc]
    _ = G.map ιD.inv ≫ ΨD.hom ≫ (εD.inv ≫ ModuleCat.ofHom P.dualMap) := by rw [hdual]
    _ = (G.map ιD.inv ≫ ΨD.hom ≫ εD.inv) ≫ ModuleCat.ofHom P.dualMap := by
      simp only [Category.assoc]

end MvPolynomial
