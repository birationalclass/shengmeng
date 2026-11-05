module
public import Linear.NativeProjectiveLaurentTransition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restricting the actual integer-twist section along the first
face changes its structure-ring coefficient by the actual (X₁/X₀)^k. -/
theorem coordinateNativeIntegerTwistCechFactorFrame_symm_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (k : ℤ)
    (s : Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n (a.delete 0).1) :
    (coordinateNativeIntegerTwistCechFactorFrame (K := K) a.1 k).symm
      ((Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) k)).map
          (coordinateOpenCechDelete (R := K) a 0).op s) =
    (show Γ(Proj (homogeneousSubmodule σ K), coordinateOpenCechIntersection (R := K) a.1) from
      Units.val ((LinearStudy.nativeCoordinateRatioUnit (homogeneousSubmodule σ K)
        (X (a.1 1).down) (X_mem_homogeneousSubmodule_one K (a.1 1).down)
        (X (a.1 0).down) (X_mem_homogeneousSubmodule_one K (a.1 0).down)
        (op (coordinateOpenCechIntersection (R := K) a.1))
        (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 1)
        (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 0))^k)) *
    (show Γ(Proj (homogeneousSubmodule σ K), coordinateOpenCechIntersection (R := K) a.1) from
      (Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (SheafOfModules.unit (Proj (homogeneousSubmodule σ K)).ringCatSheaf)).map
          (coordinateOpenCechDelete (R := K) a 0).op
          ((coordinateNativeIntegerTwistCechFactorFrame (K := K)
            (a.delete 0).1 k).symm s)) := by
  apply (coordinateNativeIntegerTwistCechFactorFrame (K := K) a.1 k).injective
  rw [LinearEquiv.apply_symm_apply]
  let r := (coordinateNativeIntegerTwistCechFactorFrame (K := K) (a.delete 0).1 k).symm s
  have hNat := LinearStudy.nativeIntegerTwistBaseSectionEquiv_restrict
    (homogeneousSubmodule σ K) (homogeneousProjπ (R := K) (σ := σ))
    (X (a.1 1).down) (X_mem_homogeneousSubmodule_one K (a.1 1).down) k
    (coordinateOpenCechDelete (R := K) a 0).op
    (coordinateOpenCechIntersection_coordinate_notMem (K := K) (a.delete 0).1 0) r
  change (Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
    (coordinateNativeIntegerTwist (K := K) (σ := σ) k)).map
      (coordinateOpenCechDelete (R := K) a 0).op
      (coordinateNativeIntegerTwistCechFactorFrame (K := K) (a.delete 0).1 k r) = _ at hNat
  rw [show coordinateNativeIntegerTwistCechFactorFrame (K := K) (a.delete 0).1 k r = s
    from LinearEquiv.apply_symm_apply _ s] at hNat
  exact hNat.trans (LinearStudy.nativeIntegerTwistSectionFrame_transition
    (homogeneousSubmodule σ K) (X (a.1 0).down) (X_mem_homogeneousSubmodule_one K (a.1 0).down)
    (X (a.1 1).down) (X_mem_homogeneousSubmodule_one K (a.1 1).down) k
    (op (coordinateOpenCechIntersection (R := K) a.1))
    (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 0)
    (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 1) _)

/-- Reindexing the first-face Laurent restriction and multiplying by
the actual frame-transition monomial preserves the global weight. -/
theorem coordinateNativeFirstLaurentWeight_reindex [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (k : ℤ)
    (y : AddMonoidAlgebra
      Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
      (laurentExponentSubmonoid (coordinateTailExponent (fun l => ((a.delete 0).1 l).down)))) :
    AddMonoidAlgebra.mapDomainLinearEquiv
      Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
      Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
      (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) k)
      (AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a k) 1 *
        AddMonoidAlgebra.mapDomain (coordinateLaurentExponentDeleteZeroAddMonoidHom a) y) =
    coordinateHomogeneousLaurentDeleteLinearMap (R := K) a 0 k
      (AddMonoidAlgebra.mapDomainLinearEquiv
        Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
        Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
        (coordinateLaurentExponentEquiv (fun l => ((a.delete 0).1 l).down) k) y) := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz =>
      simp only [AddMonoidAlgebra.mapDomain_add, mul_add, map_add, hy, hz]
  | single e c =>
      simp only [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single,
        one_mul, AddMonoidAlgebra.mapDomainLinearEquiv_single,
        coordinateHomogeneousLaurentDeleteLinearMap_single]
      apply congrArg (fun t => AddMonoidAlgebra.single t c)
      exact (congrArg (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) k)
        (add_comm _ _)).trans (coordinateLaurentExponentEquiv_delete_zero_add_transition a k e)

/-- The actual first-face restriction of every integer twist is the
same global-weight inclusion as every other Cech face. -/
theorem coordinateNativeIntegerTwistCechFactorLaurentEquiv_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (k : ℤ)
    (s : Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n (a.delete 0).1) :
    coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a.1 k
      ((Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) k)).map
          (coordinateOpenCechDelete (R := K) a 0).op s) =
      coordinateHomogeneousLaurentDeleteLinearMap (R := K) a 0 k
        (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K)
          (a.delete 0).1 k s) := by
  let r := (coordinateNativeIntegerTwistCechFactorFrame (K := K) (a.delete 0).1 k).symm s
  change coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := K) a.1 k
    ((coordinateNativeIntegerTwistCechFactorFrame (K := K) a.1 k).symm _) = _
  rw [coordinateNativeIntegerTwistCechFactorFrame_symm_delete_zero]
  change AddMonoidAlgebra.mapDomainLinearEquiv
    Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
    Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
    (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) k)
    (coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := K) a.1 (_ * _)) = _
  rw [map_mul]
  have hTrans : coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := K) a.1
      (Units.val ((LinearStudy.nativeCoordinateRatioUnit (homogeneousSubmodule σ K)
        (X (a.1 1).down) (X_mem_homogeneousSubmodule_one K (a.1 1).down)
        (X (a.1 0).down) (X_mem_homogeneousSubmodule_one K (a.1 0).down)
        (op (coordinateOpenCechIntersection (R := K) a.1))
        (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 1)
        (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 0))^k)) =
        AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a k) 1 := by
    change AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
        (coordinateOpenCechIntersectionLaurentRingEquiv (R := K) a.1 _) = _
    rw [coordinateNativeFirstRatio_zpow_laurent, AddMonoidAlgebra.mapRingEquiv_single, map_one]
  rw [hTrans]
  change AddMonoidAlgebra.mapDomainLinearEquiv
    Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
    Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
    (coordinateLaurentExponentEquiv (fun l => (a.1 l).down) k)
    (AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a k) 1 *
      coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := K) a.1
        ((Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
          (SheafOfModules.unit (Proj (homogeneousSubmodule σ K)).ringCatSheaf)).map
            (coordinateOpenCechDelete (R := K) a 0).op r)) = _
  rw [coordinateOpenCechIntersectionBaseLaurentLinearEquiv_naturality_delete_zero]
  exact coordinateNativeFirstLaurentWeight_reindex (K := K) a k _

/-- All actual ordered Cech restrictions of the native integer twist
commute with its global homogeneous Laurent factor equivalences. -/
theorem coordinateNativeIntegerTwistCechFactorLaurentEquiv_delete
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : Fin (n + 2)) (k : ℤ)
    (s : Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n (a.delete j).1) :
    coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a.1 k
      ((Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) k)).map
          (coordinateOpenCechDelete (R := K) a j).op s) =
      coordinateHomogeneousLaurentDeleteLinearMap (R := K) a j k
        (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) (a.delete j).1 k s) := by
  cases j using Fin.cases with
  | zero => exact coordinateNativeIntegerTwistCechFactorLaurentEquiv_delete_zero a k s
  | succ j => exact coordinateNativeIntegerTwistCechFactorLaurentEquiv_delete_succ a j k s
end MvPolynomial
