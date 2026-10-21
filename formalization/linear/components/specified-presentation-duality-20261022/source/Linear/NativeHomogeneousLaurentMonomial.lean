module
public import Linear.NativeHomogeneousLaurentSection
public import Linear.ProjectiveHomogeneousMonomialLaurent
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance nativeSectionMonomialDecidableEq : DecidableEq σ := Classical.decEq σ

/-- An original homogeneous monomial has its original global Laurent
weight on every actual coordinate intersection. -/
theorem coordinateNativeHomogeneousMonomial_laurent {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (e : HomogeneousLaurentExponent σ (m : ℤ)) (he : ∀ i, 0 ≤ e.1 i) (c : K) :
    coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a (m : ℤ)
      ((Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (m : ℤ))).map
          (homOfLE (show coordinateOpenCechIntersection (R := K) a ≤ ⊤ from le_top)).op
          (LinearStudy.nativePositiveHomogeneousGlobalSection
            (homogeneousSubmodule σ K) m
              ⟨monomial e.natExponent c,e.natExponent_monomial_homogeneous m he c⟩)) =
      AddMonoidAlgebra.single
        (⟨e,e.isAllowedOn_of_nonnegative he (fun j => (a j).down)⟩ :
          {e : HomogeneousLaurentExponent σ (m : ℤ) //
            e.IsAllowedOn (fun j => (a j).down)})
        ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm c) := by
  rw [coordinateNativeHomogeneousGlobalSection_laurent,
    dehomogenizeAux_monomial_chart]
  change AddMonoidAlgebra.mapDomain _
    (AddMonoidAlgebra.mapRingEquiv _ _
      (AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single _ c))) = _
  rw [AddMonoidAlgebra.mapDomain_single,AddMonoidAlgebra.mapRingEquiv_single,
    AddMonoidAlgebra.mapDomain_single]
  congr 1
  exact coordinateLaurentExponentEquiv_natChart (fun j => (a j).down) m e he
end MvPolynomial
