module
public import Linear.NativeHomogeneousLaurentMonomial
public import Linear.NativeProjectiveLaurentComplex
import all Linear.ProjectiveLaurentWeightComponents
import all Mathlib.CategoryTheory.Limits.HasLimits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- One compatible nonnegative Laurent weight is the actual restriction
of its ORIGINAL degree-m monomial, with its ORIGINAL coefficient field. -/
theorem coordinateNativeLaurentZeroCycle_monomial_component
    (m : ℕ) (j : σ)
    (x : coordinateHomogeneousLaurentOrderedCechObject (R := K) (σ := σ) (m : ℤ) 0)
    (hx : (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := K) (σ := σ) (m : ℤ) 0).hom x = 0)
    (e : HomogeneousLaurentExponent σ (m : ℤ)) (he : ∀ i, 0 ≤ e.1 i) :
    (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) (m : ℤ) 0).hom
      (Scheme.Modules.orderedBaseCechAugmentation (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (m : ℤ))
        (coordinateOpenCover (R := K) (σ := σ))
        (LinearStudy.nativePositiveHomogeneousGlobalSection (homogeneousSubmodule σ K) m
          ⟨monomial e.natExponent
              ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
                ((coordinateHomogeneousLaurentWeightComponent (R := K) (m : ℤ) e 0 x).1
                  (Scheme.Modules.orderedCechSingleton (ULift.up j)))),
            (mem_homogeneousSubmodule m _).mpr (e.natExponent_monomial_homogeneous m he _)⟩)) =
      coordinateHomogeneousLaurentWeightInclusion (R := K) (m : ℤ) e 0
        (coordinateHomogeneousLaurentWeightComponent (R := K) (m : ℤ) e 0 x) := by
  apply Concrete.limit_ext (Discrete.functor fun
    a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0 =>
      coordinateHomogeneousLaurentWeightFactor (R := K) (m : ℤ) a)
  intro a
  rcases a with ⟨a⟩
  change (coordinateHomogeneousLaurentWeightProjection (R := K) (m : ℤ) a).hom
      ((coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) (m : ℤ) 0).hom
        (Scheme.Modules.orderedBaseCechAugmentation _ _ _ _)) =
      (coordinateHomogeneousLaurentWeightProjection (R := K) (m : ℤ) a).hom
        (coordinateHomogeneousLaurentWeightInclusion (R := K) (m : ℤ) e 0
          (coordinateHomogeneousLaurentWeightComponent (R := K) (m : ℤ) e 0 x))
  rw [coordinateHomogeneousLaurentWeightProjection_inclusion_apply,
    coordinateHomogeneousLaurentWeightSingle_apply_of_allowed
      (h := e.isAllowedOn_of_nonnegative he (fun k => (a.1 k).down))]
  unfold coordinateHomogeneousLaurentWeightProjection coordinateNativeLaurentOrderedCechObjectIso
  change ((Scheme.Modules.orderedBaseCechAugmentation _ _ _ ≫
      (Pi.mapIso (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0 =>
        (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) b.1 (m : ℤ)).toModuleIso)).hom ≫
      Pi.π _ a) _) = _
  erw [Pi.mapIso_hom_π,Scheme.Modules.orderedBaseCechAugmentation_comp_π_assoc]
  change coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a.1 (m : ℤ)
    ((Scheme.Modules.baseModulePresheaf _ _).map (homOfLE le_top).op _) = _
  rw [coordinateNativeHomogeneousMonomial_laurent a.1 m e he _, RingEquiv.symm_apply_apply]
  congr 1
  exact (coordinateHomogeneousLaurentZeroCycle_component_constant
    (R := K) (m : ℤ) e j x hx a).symm
end MvPolynomial
