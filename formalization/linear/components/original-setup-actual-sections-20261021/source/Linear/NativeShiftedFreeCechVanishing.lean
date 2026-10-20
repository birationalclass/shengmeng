module
public import Linear.NativeShiftedFreeIntegerTwistBiproduct
public import Linear.ModuleOrderedCechFiniteBiproduct
public import Linear.NativeProjectiveTwistCechVanishing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open LinearStudy AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every integer twist above all generator degrees of an actual finite
shifted free module has an exact actual ordered coordinate Cech complex
in every positive degree. No sheaf comparison or exactness is assumed. -/
theorem coordinateNativeShiftedFree_orderedCech_exactAt_succ
    (j : σ) (w : ι → ℤ) (k : ℤ) (hk : ∀ i, w i ≤ k) (q : ℕ) :
    (Scheme.Modules.orderedBaseCechComplex
      (homogeneousProjπ (R := K) (σ := σ))
      (nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
        (integerShiftedFreePiece (homogeneousSubmodule σ K) w)
        (integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) w) k)
      (coordinateOpenCover (R := K) (σ := σ))).ExactAt (q+1) := by
  letI : HasFiniteBiproducts (Proj (homogeneousSubmodule σ K)).Modules :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let G : ι → (Proj (homogeneousSubmodule σ K)).Modules :=
    fun i => coordinateNativeIntegerTwist (K := K) (σ := σ) (k-w i)
  have hG := Scheme.Modules.orderedBaseCechComplex_coproduct_exactAt
    (homogeneousProjπ (R := K) (σ := σ))
    (coordinateOpenCover (R := K) (σ := σ)) G (q+1)
    (fun i => coordinateNativeIntegerTwist_orderedBaseCechComplex_exactAt_succ
      (K := K) j (k-w i) (sub_nonneg.mpr (hk i)) q)
  let e := nativeShiftedFreeIntegerTwistBiproductIso (homogeneousSubmodule σ K) w k
  let ec := e ≪≫ biproduct.isoCoproduct G
  exact hG.of_iso ((Scheme.Modules.orderedBaseCechComplexFunctor
    (homogeneousProjπ (R := K) (σ := σ))
    (coordinateOpenCover (R := K) (σ := σ))).mapIso ec).symm

/-- A constructed bound depending only on the actual finite generator
degrees suffices simultaneously for every positive Cech degree. -/
theorem coordinateNativeShiftedFree_eventually_orderedCech_exactAt_succ
    (j : σ) (w : ι → ℤ) :
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N → ∀ q : ℕ,
      (Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := K) (σ := σ))
        (nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
          (integerShiftedFreePiece (homogeneousSubmodule σ K) w)
          (integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) w) N)
        (coordinateOpenCover (R := K) (σ := σ))).ExactAt (q+1) := by
  classical
  refine ⟨Finset.univ.sup (fun i => (w i).toNat), fun N hN q => ?_⟩
  apply coordinateNativeShiftedFree_orderedCech_exactAt_succ j w N _ q
  intro i
  have hi := Finset.le_sup (f := fun i => (w i).toNat) (Finset.mem_univ i)
  omega

end MvPolynomial
