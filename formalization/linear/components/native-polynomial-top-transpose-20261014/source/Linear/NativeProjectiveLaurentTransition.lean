module
public import Linear.NativeProjectiveLaurentNoninitial
public import Linear.ProjectiveLaurentInitialRestriction
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
local instance : DecidableEq σ := Classical.decEq σ

/-- The actual coordinate-ratio section is the restriction of the
degree-zero chart coordinate under the canonical Proj chart isomorphism. -/
theorem coordinateNativeRatioSection_eq_awayVar (i : σ) (j : {j : σ // j ≠ i})
    (U : (Proj (homogeneousSubmodule σ K)).Opens)
    (hU : U ≤ Proj.basicOpen (homogeneousSubmodule σ K) (X i)) :
    LinearStudy.nativeCoordinateRatioSection (homogeneousSubmodule σ K)
      (X j.1) (X_mem_homogeneousSubmodule_one K j.1)
      (X i) (X_mem_homogeneousSubmodule_one K i) (op U)
      (fun p => hU p.2) =
    (Proj (homogeneousSubmodule σ K)).presheaf.map (homOfLE hU).op
      ((Proj.basicOpenIsoAway (homogeneousSubmodule σ K) (X i)
        (X_mem_homogeneousSubmodule_one K i) one_pos).hom.hom (awayVar K i j)) := by
  apply Subtype.ext
  funext p
  change HomogeneousLocalization.mk _ =
    HomogeneousLocalization.mapId (homogeneousSubmodule σ K)
      (Submonoid.powers_le.mpr (hU p.2)) (awayVar K i j)
  simp only [awayVar, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.mapId, HomogeneousLocalization.map_mk, pow_one]
  rfl

/-- In the actual structure-ring Laurent coordinates, the first
native frame transition is the monomial in the second chart variable. -/
theorem coordinateNativeFirstRatio_laurent [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := K) a.1
      (LinearStudy.nativeCoordinateRatioSection (homogeneousSubmodule σ K)
        (X (a.1 1).down) (X_mem_homogeneousSubmodule_one K (a.1 1).down)
        (X (a.1 0).down) (X_mem_homogeneousSubmodule_one K (a.1 0).down)
        (op (coordinateOpenCechIntersection (R := K) a.1))
        (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 0)) =
      AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a 1) 1 := by
  let j : {j : σ // j ≠ (a.1 0).down} :=
    ⟨(a.1 1).down, coordinateOpenCechFirstSecond_ne a⟩
  let q := awayVar K (a.1 0).down j
  have hNat := ConcreteCategory.congr_hom
    (coordinateOpenCechIntersectionAwayIso_naturality_firstChart (R := K) a.1) q
  have hq : (coordinateOpenCechIntersectionAwayIso (R := K) a.1).inv.hom
      (LinearStudy.nativeCoordinateRatioSection (homogeneousSubmodule σ K)
        (X (a.1 1).down) (X_mem_homogeneousSubmodule_one K (a.1 1).down)
        (X (a.1 0).down) (X_mem_homogeneousSubmodule_one K (a.1 0).down)
        (op (coordinateOpenCechIntersection (R := K) a.1))
        (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 0)) =
      coordinateTargetTailAwayMap (R := K) a q := by
    apply (coordinateOpenCechIntersectionAwayIso (R := K) a.1).commRingCatIsoToRingEquiv.injective
    change (coordinateOpenCechIntersectionAwayIso (R := K) a.1).hom.hom
      ((coordinateOpenCechIntersectionAwayIso (R := K) a.1).inv.hom
        (LinearStudy.nativeCoordinateRatioSection (homogeneousSubmodule σ K)
          (X (a.1 1).down) (X_mem_homogeneousSubmodule_one K (a.1 1).down)
          (X (a.1 0).down) (X_mem_homogeneousSubmodule_one K (a.1 0).down)
          (op (coordinateOpenCechIntersection (R := K) a.1))
          (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 0))) =
      (coordinateOpenCechIntersectionAwayIso (R := K) a.1).hom.hom
        (coordinateTargetTailAwayMap (R := K) a q)
    rw [Iso.inv_hom_id_apply]
    rw [coordinateNativeRatioSection_eq_awayVar (K := K) (a.1 0).down j
      (coordinateOpenCechIntersection (R := K) a.1)
      (coordinateOpenCechIntersection_le (R := K) a.1 0)]
    exact hNat.symm
  change laurentMonomialRingEquiv K (coordinateTailExponent (fun l => (a.1 l).down))
    (coordinateProductAwayRingEquiv (R := K) (fun l => (a.1 l).down)
      ((coordinateOpenCechIntersectionAwayIso (R := K) a.1).inv.hom _)) = _
  rw [hq, coordinateTargetTailAwayMap_awayVar_laurent]
  apply congrArg (fun e => AddMonoidAlgebra.single e (1 : K))
  apply Subtype.ext
  ext i
  rw [laurentExponentAwayMap_apply]
  change ((Finsupp.single j 1 i : ℕ) : ℤ) = Finsupp.single j 1 i
  by_cases hi : i = j
  · subst i
    simp
  · simp [hi]

/- The following two pure Laurent-unit constructions adapt AINTLIB
ProjectiveSpaceTwistCech.lean:1260-1316 at commit
ab1451487da02cd4483d0e2cdb2cc9e44bbbac17 (Apache 2.0).
The geometric transition below uses our actual native ratio section. -/
def coordinateNativeFirstLaurentUnit [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    (AddMonoidAlgebra K (laurentExponentSubmonoid
      (coordinateTailExponent (fun l => (a.1 l).down))))ˣ where
  val := AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a 1) 1
  inv := AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a (-1)) 1
  val_inv := by
    rw [AddMonoidAlgebra.single_mul_single, ← map_add]
    norm_num
    exact AddMonoidAlgebra.one_def.symm
  inv_val := by
    rw [AddMonoidAlgebra.single_mul_single, ← map_add]
    norm_num
    exact AddMonoidAlgebra.one_def.symm

theorem coordinateNativeFirstLaurentUnit_zpow [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (k : ℤ) :
    ((coordinateNativeFirstLaurentUnit (K := K) a ^ k :
      (AddMonoidAlgebra K (laurentExponentSubmonoid
        (coordinateTailExponent (fun l => (a.1 l).down))))ˣ) :
        AddMonoidAlgebra K (laurentExponentSubmonoid
          (coordinateTailExponent (fun l => (a.1 l).down)))) =
      AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a k) 1 := by
  cases k with
  | ofNat m =>
      have hn := congrArg Units.val
        (zpow_natCast (coordinateNativeFirstLaurentUnit (K := K) a) m)
      change (↑(coordinateNativeFirstLaurentUnit (K := K) a ^ (m : ℤ)) :
        AddMonoidAlgebra K (laurentExponentSubmonoid
          (coordinateTailExponent (fun l => (a.1 l).down)))) = _
      rw [hn, Units.val_pow_eq_pow_val]
      change (AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a 1) 1)^m = _
      rw [AddMonoidAlgebra.single_pow, one_pow, ← map_nsmul]
      congr
      simp
  | negSucc m =>
      rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      change (AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a (-1)) 1)^(m+1) = _
      rw [AddMonoidAlgebra.single_pow, one_pow, ← map_nsmul]
      congr
      simp [Int.negSucc_eq]

/-- Every integer power of the actual native transition has the
corresponding single Laurent monomial as its actual geometric image. -/
theorem coordinateNativeFirstRatio_zpow_laurent [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (k : ℤ) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := K) a.1
      (Units.val ((LinearStudy.nativeCoordinateRatioUnit (homogeneousSubmodule σ K)
        (X (a.1 1).down) (X_mem_homogeneousSubmodule_one K (a.1 1).down)
        (X (a.1 0).down) (X_mem_homogeneousSubmodule_one K (a.1 0).down)
        (op (coordinateOpenCechIntersection (R := K) a.1))
        (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 1)
        (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 0))^k)) =
      AddMonoidAlgebra.single (coordinateOpenCechFirstTransitionExponent a k) 1 := by
  let f := (coordinateOpenCechIntersectionLaurentRingEquiv (R := K) a.1).toRingHom
  let t := LinearStudy.nativeCoordinateRatioUnit (homogeneousSubmodule σ K)
    (X (a.1 1).down) (X_mem_homogeneousSubmodule_one K (a.1 1).down)
    (X (a.1 0).down) (X_mem_homogeneousSubmodule_one K (a.1 0).down)
    (op (coordinateOpenCechIntersection (R := K) a.1))
    (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 1)
    (coordinateOpenCechIntersection_coordinate_notMem (K := K) a.1 0)
  have ht : Units.map f.toMonoidHom t = coordinateNativeFirstLaurentUnit (K := K) a := by
    apply Units.ext
    exact coordinateNativeFirstRatio_laurent (K := K) a
  change f (Units.val (t^k)) = _
  calc
    _ = ↑(Units.map f.toMonoidHom (t^k)) := (Units.coe_map f.toMonoidHom (t^k)).symm
    _ = ↑((Units.map f.toMonoidHom t)^k) :=
      congrArg Units.val ((Units.map f.toMonoidHom).map_zpow t k)
    _ = _ := by
      simpa only [ht] using coordinateNativeFirstLaurentUnit_zpow (K := K) a k
end MvPolynomial
