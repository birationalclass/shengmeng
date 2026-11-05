module
public import Linear.NativeIntegerTwistedPresentationCechHomDuality
public import Linear.NativeIntegerTwistedFreeFamilyHomDuality
public import Linear.IntegerTwistedPresentationCoefficientDualMap
public import Linear.IntegerShiftedFreeRegradingPresentation
public import Linear.NativeProjectiveTwistRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
attribute [local instance] MvPolynomial.gradedAlgebra

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (β : (J → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    z d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    w d)
variable (hβ : ∀ d : ℤ, ∀ x : J → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    w d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
variable (n : ℕ) (hcard : Fintype.card σ=n+2)

/-- For EVERY original integer k,the ACTUAL comparison of SAME original
native M(k) preserves ORIGINAL beta. The coefficient map is original
phi(beta(e_j)) at degree -N-k. Primal sheaf and contravariant coefficient
regrading squares are PROVED and reused;no twist/map comparison is an
input. Original Koszul connecting and derived SHEAF cohomology remain
separate obligations. -/
theorem coordinateNativeIntegerTwistedPresentationGradedHomDualIso_quotient (k : ℤ) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w) D
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) w)
          hD β hβ k)) ≫
      (coordinateNativeIntegerTwistedPresentationGradedHomDualIso
        z w D hD c β hc hβ honto hex n hcard k).hom =
    (coordinateNativeIntegerTwistedFreeFamilyCoefficientDualIso w k n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreePresentationHomCoefficientMap c
        (homogeneousSubmodule σ K) z w hc D β hβ honto hex
        (-(Fintype.card σ:ℤ)-k)).dualMap := by
  let B := homogeneousSubmodule σ K
  let G := (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n) ⋙
    ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let Dk := LinearStudy.integerGradingShift D k
  let hDk := LinearStudy.integerGradingShift_smul_homogeneous B D hD k
  letI : DirectSum.Decomposition Dk := LinearStudy.integerGradingShiftDecomposition D k
  let zk := fun i => z i-k
  let wk := fun j => w j-k
  let hck := LinearStudy.integerShiftedFreeRelation_regrade B z w c hc k
  let hβk := LinearStudy.integerShiftedFreeQuotient_regrade B w D β hβ k
  let γw := LinearStudy.nativeIntegerFreeTwistRegradingIso B w k
  let γM := LinearStudy.nativeProjectiveTwistRegradingIso B D hD k
  let b := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B w) D
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B w) hD β hβ k
  let bk := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B wk) Dk
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B wk) hDk β hβk 0
  let Ψ := coordinateNativeIntegerPresentationGradedHomDualIso
    zk wk Dk hDk c β hck hβk honto hex n hcard
  let Φw := coordinateNativeIntegerFreeFamilyCoefficientDualIso (K := K) (σ := σ) wk n hcard
  let εM := (LinearStudy.integerGradedHomRegradingEquiv B D k
    (-(Fintype.card σ:ℤ))).dualMap.toModuleIso
  let εw := (LinearStudy.integerShiftedFreeDualCoordinateRegradingEquiv B w k
    (-(Fintype.card σ:ℤ))).dualMap.toModuleIso
  let αk := ModuleCat.ofHom (LinearStudy.integerShiftedFreePresentationHomCoefficientMap
    c B zk wk hck Dk β hβk honto hex (-(Fintype.card σ:ℤ))).dualMap
  let α := ModuleCat.ofHom (LinearStudy.integerShiftedFreePresentationHomCoefficientMap
    c B z w hc D β hβ honto hex (-(Fintype.card σ:ℤ)-k)).dualMap
  have hprimal : γw.inv ≫ bk ≫ γM.hom = b :=
    LinearStudy.nativeIntegerFreeTwistRegradingIso_quotient B w D hD β hβ k
  have hb : G.map b ≫ G.map γM.inv = G.map γw.inv ≫ G.map bk := by
    have hbm : b ≫ γM.inv = γw.inv ≫ bk := by
      rw [← hprimal]
      simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    rw [← G.map_comp,hbm,G.map_comp]
  have hquot := coordinateNativeIntegerPresentationGradedHomDualIso_quotient
    zk wk Dk hDk c β hck hβk honto hex n hcard
  change G.map bk ≫ Ψ.hom = Φw.hom ≫ αk at hquot
  have hdual : αk ≫ εM.inv = εw.inv ≫ α :=
    LinearStudy.integerTwistedPresentationCoefficientDualMap B z w D c β hc hβ honto hex
      k (-(Fintype.card σ:ℤ))
  change G.map b ≫ _ = _ ≫ α
  calc
    G.map b ≫ (coordinateNativeIntegerTwistedPresentationGradedHomDualIso
        z w D hD c β hc hβ honto hex n hcard k).hom =
      (G.map b ≫ G.map γM.inv) ≫ Ψ.hom ≫ εM.inv := by
        simp only [coordinateNativeIntegerTwistedPresentationGradedHomDualIso,
          Iso.trans_hom,Iso.symm_hom,Functor.mapIso_inv,Category.assoc]
        rfl
    _ = G.map γw.inv ≫ (G.map bk ≫ Ψ.hom) ≫ εM.inv := by
      rw [hb]
      simp only [Category.assoc]
    _ = G.map γw.inv ≫ (Φw.hom ≫ αk) ≫ εM.inv := by rw [hquot]
    _ = G.map γw.inv ≫ Φw.hom ≫ εw.inv ≫ α := by
      simp only [Category.assoc]
      rw [hdual]
    _ = (coordinateNativeIntegerTwistedFreeFamilyCoefficientDualIso w k n hcard).hom ≫ α := by
      rfl

end MvPolynomial
