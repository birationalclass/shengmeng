module
public import Linear.IntegerGradedEndZero
public import Linear.NativeCoextensionSpecifiedEvaluationTrace
public import Linear.IntegerGradedHomPieceFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [IsDomain S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  coextensionGradedDecomposition coextensionOriginalBaseScalarTower
  coextensionTraceBaseSourceTower coextensionTraceFieldSourceTower coextensionTraceFiniteBase
/-- Evaluate ACTUAL degree-zero upper-linear endomorphisms of the SAME
coextension at the ORIGINAL eval-at-one functional. The target is the SAME
original homogeneous Hom piece,not a newly transported scalar structure. -/
def coextensionDegreeZeroEndEvaluation :
    integerGradedEndZero (S:=S) (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) →ₗ[K]
      integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K)
        (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) 0 where
  toFun f := ⟨(coextensionOriginalEvaluationAtOne (R:=(MvPolynomial σ K)) (S:=S)).comp
    (f.1.restrictScalars (MvPolynomial σ K)),by
      intro j ell hell
      exact (coextensionOriginalEvaluationAtOne_mem_integerGradedHomPiece
        (MvPolynomial.homogeneousSubmodule σ K) B) j (f.1 ell) (f.property j ell hell)⟩
  map_add' f g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro ell
    rfl
  map_smul' k f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro ell
    change coextensionOriginalEvaluationAtOne (R:=(MvPolynomial σ K)) (S:=S) (k • f.1 ell)=
      k • coextensionOriginalEvaluationAtOne (R:=(MvPolynomial σ K)) (S:=S) (f.1 ell)
    exact (coextensionOriginalEvaluationAtOne (R:=(MvPolynomial σ K)) (S:=S)).map_smul_of_tower k _
/-- The ACTUAL coextension adjunction proves injectivity of evaluation:
its value on s*ell recovers the original upper-linear map at ell and s.
No scalarity or nondegeneracy is assumed. -/
theorem coextensionDegreeZeroEndEvaluation_injective :
    Function.Injective (coextensionDegreeZeroEndEvaluation (σ:=σ) B) := by
  intro f g h
  let A := (ModuleCat.restrictCoextendScalarsAdj (algebraMap (MvPolynomial σ K) S)).homEquiv
    (ModuleCat.of S ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))))
    (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))
  have hh : A.symm (ModuleCat.ofHom f.1)=A.symm (ModuleCat.ofHom g.1) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ell
    exact congrArg (fun phi => phi.1 ell) h
  have he := A.symm.injective hh
  apply Subtype.ext
  exact congrArg ModuleCat.Hom.hom he
/-- Finite dimensionality of the ACTUAL degree-zero endomorphism algebra
is DERIVED from the existing homogeneous-Hom finiteness theorem and the
original injective evaluation. It is not a supplied rigidity premise. -/
theorem coextensionDegreeZeroEnd_finite :
    Module.Finite K (integerGradedEndZero (S:=S)
      (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)) := by
  let V : Type := integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K)
    (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) 0
  letI : Module.Finite K V := polynomialIntegerGradedHomPiece_finite
    (K:=K) (σ:=σ) (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) 0
  letI : IsNoetherian K V := by
    convert! (isNoetherian_of_isNoetherianRing_of_finite K V) using 1
  exact Module.Finite.of_injective (R:=K) (S:=K) (coextensionDegreeZeroEndEvaluation (σ:=σ) B)
    (coextensionDegreeZeroEndEvaluation_injective (σ:=σ) B)
end LinearStudy
