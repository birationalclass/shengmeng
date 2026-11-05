module
public import Linear.NativeHomogeneousSectionFrame
public import Linear.NativeProjectiveLaurentFactors
public import Linear.ProjectiveCechLaurentRestriction
import all Linear.ProjectiveCechLaurentSections
import all Mathlib.Algebra.MonoidAlgebra.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance nativeHomogeneousSectionDecidableEq : DecidableEq σ := Classical.decEq σ

private theorem nativePolynomial_mapDomainLinearEquiv_apply
    {A B : Type*} {C : Type*} [CommRing C] (e : A ≃ B) (x : AddMonoidAlgebra C A) :
    AddMonoidAlgebra.mapDomainLinearEquiv C C e x = AddMonoidAlgebra.mapDomain e x := by
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.coeff_mapDomainLinearEquiv]
  exact Finsupp.equivMapDomain_eq_mapDomain e x.coeff

/-- The actual chart Laurent expansion of an original homogeneous
polynomial section is its dehomogenization, reindexed by global weights.
The comparison is proved on the original localizations and restrictions. -/
theorem coordinateNativeHomogeneousGlobalSection_laurent {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (ell : homogeneousSubmodule σ K m) :
    coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a (m : ℤ)
      ((Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (m : ℤ))).map
          (homOfLE (show coordinateOpenCechIntersection (R := K) a ≤ ⊤ from le_top)).op
          (LinearStudy.nativePositiveHomogeneousGlobalSection
            (homogeneousSubmodule σ K) m ell)) =
      AddMonoidAlgebra.mapDomain
        (coordinateLaurentExponentEquiv (fun j => (a j).down) (m : ℤ))
        (AddMonoidAlgebra.mapRingEquiv _
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
          (AddMonoidAlgebra.mapDomain
            (laurentExponentAwayMap (coordinateTailExponent (fun j => (a j).down))).toAddMonoidHom
            (dehomogenizeAux K (a 0).down (ell : MvPolynomial σ K)))) := by
  let q := HomogeneousLocalization.Away.mk (homogeneousSubmodule σ K)
    (X_mem_homogeneousSubmodule_one K (a 0).down) m (ell : MvPolynomial σ K)
    (by simpa using ell.property)
  let c := ((Proj (homogeneousSubmodule σ K)).presheaf.map
    (homOfLE (coordinateOpenCechIntersection_le (R := K) a 0)).op).hom
    ((Proj.basicOpenIsoAway (homogeneousSubmodule σ K) (X (a 0).down)
      (X_mem_homogeneousSubmodule_one K (a 0).down) one_pos).hom.hom q)
  have hframe : coordinateNativeIntegerTwistCechFactorFrame (K := K) a (m : ℤ) c =
      (Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (m : ℤ))).map
        (homOfLE (show coordinateOpenCechIntersection (R := K) a ≤ ⊤ from le_top)).op
        (LinearStudy.nativePositiveHomogeneousGlobalSection
          (homogeneousSubmodule σ K) m ell) :=
    LinearStudy.nativePositiveHomogeneousGlobalSection_frame
      (homogeneousSubmodule σ K) m ell (X (a 0).down)
      (X_mem_homogeneousSubmodule_one K (a 0).down)
      (coordinateOpenCechIntersection (R := K) a)
      (coordinateOpenCechIntersection_le (R := K) a 0)
  rw [← hframe]
  change coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := K) a (m : ℤ)
    ((coordinateNativeIntegerTwistCechFactorFrame (K := K) a (m : ℤ)).symm
      (coordinateNativeIntegerTwistCechFactorFrame (K := K) a (m : ℤ) c)) = _
  rw [LinearEquiv.symm_apply_apply]
  have hNat := ConcreteCategory.congr_hom
    (coordinateOpenCechIntersectionAwayIso_naturality_firstChart (R := K) a) q
  have hq : (coordinateOpenCechIntersectionAwayIso (R := K) a).inv.hom c =
      HomogeneousLocalization.awayMap (homogeneousSubmodule σ K)
        (coordinateTailPolynomial_mem (R := K) (fun j => (a j).down)) rfl q := by
    apply (coordinateOpenCechIntersectionAwayIso (R := K) a).commRingCatIsoToRingEquiv.injective
    change (coordinateOpenCechIntersectionAwayIso (R := K) a).hom.hom
      ((coordinateOpenCechIntersectionAwayIso (R := K) a).inv.hom c) =
      (coordinateOpenCechIntersectionAwayIso (R := K) a).hom.hom
        (HomogeneousLocalization.awayMap (homogeneousSubmodule σ K)
          (coordinateTailPolynomial_mem (R := K) (fun j => (a j).down)) rfl q)
    rw [Iso.inv_hom_id_apply]
    exact hNat.symm
  unfold coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
  rw [LinearEquiv.trans_apply]
  unfold coordinateOpenCechIntersectionBaseLaurentLinearEquiv
  unfold coordinateOpenCechIntersectionBaseCechFactorAddEquiv
    coordinateOpenCechIntersectionBaseLaurentRingEquiv
    coordinateOpenCechIntersectionLaurentRingEquiv
  rw [nativePolynomial_mapDomainLinearEquiv_apply]
  change AddMonoidAlgebra.mapDomain
    (coordinateLaurentExponentEquiv (fun j => (a j).down) (m : ℤ))
    (AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
      (laurentMonomialRingEquiv K (coordinateTailExponent (fun j => (a j).down))
        (coordinateProductAwayRingEquiv (R := K) (fun j => (a j).down)
          ((coordinateOpenCechIntersectionAwayIso (R := K) a).inv.hom c)))) = _
  rw [hq]
  erw [coordinateProductAwayLaurentRingEquiv_awayMap (R := K) (fun j => (a j).down) q]
  have hdehom : chartRingEquiv K (a 0).down q =
      dehomogenizeAux K (a 0).down (ell : MvPolynomial σ K) :=
    dehomogenizeAt_mk K (a 0).down (by simpa using ell.property)
  rw [hdehom]
end MvPolynomial
