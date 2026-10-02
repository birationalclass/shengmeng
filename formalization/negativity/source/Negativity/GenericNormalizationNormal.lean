module

public import Negativity.FiniteNormalizationGeometry
public import Negativity.NormalSections
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem relative_integralClosure_isIntegrallyClosed
    (A K S : Type*) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing S] [Algebra A S] (j : S →ₐ[A] K) (hj : Function.Bijective j) :
    IsIntegrallyClosed (integralClosure A S) := by
  let C := integralClosure A S
  let e := AlgEquiv.ofBijective j hj
  let : Algebra C K := (j.toRingHom.comp C.val.toRingHom).toAlgebra
  have : IsScalarTower A C K := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (j.commutes a).symm)
  have : IsIntegralClosure C A K := {
    algebraMap_injective := hj.injective.comp Subtype.val_injective
    isIntegral_iff := by
      intro x
      constructor
      · intro hx
        exact ⟨⟨e.symm x, hx.map e.symm.toAlgHom⟩, e.apply_symm_apply x⟩
      · rintro ⟨y, rfl⟩
        exact y.property.map j }
  have : IsIntegrallyClosed (integralClosure A K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  exact IsIntegrallyClosed.of_equiv
    (IsIntegralClosure.equiv A (integralClosure A K) K C).toRingEquiv

/-- Actual affine sections of normalization are normal: their actual
relative closure is identified with the integral closure in the generic
field, rather than postulating normality of the glued scheme. -/
theorem generic_normalization_affine_sections_normal
    (Y : Scheme.{u}) [IsIntegral Y]
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ((Y.fromSpecStalk (genericPoint Y)).normalization,
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization ⁻¹ᵁ U) := by
  let f := Y.fromSpecStalk (genericPoint Y)
  let : Algebra Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  obtain ⟨j, hj⟩ := generic_stalk_affine_functionField_embedding Y U
  have : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  have : IsIntegrallyClosed (integralClosure Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U)) :=
    relative_integralClosure_isIntegrallyClosed _ _ _ j hj
  let e := RingEquiv.ofBijective (f.normalizationObjIso hU).hom.hom
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).hom)
  exact IsIntegrallyClosed.of_equiv e.symm

/-- Final theorem: all actual stalks of generic-field normalization are
integrally closed. This holds in every dimension and characteristic. -/
theorem generic_normalization_stalks_normal (Y : Scheme.{u}) [IsIntegral Y] :
    ∀ z : (Y.fromSpecStalk (genericPoint Y)).normalization,
      IsIntegrallyClosed
        ((Y.fromSpecStalk (genericPoint Y)).normalization.presheaf.stalk z) := by
  let f := Y.fromSpecStalk (genericPoint Y)
  intro z
  obtain ⟨U, hU, hyU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f.fromNormalization z) trivial
  have : Nonempty U := ⟨⟨f.fromNormalization z, hyU⟩⟩
  let V := f.fromNormalization ⁻¹ᵁ U
  have hzV : z ∈ V := hyU
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have hV : IsAffineOpen V := hU.preimage f.fromNormalization
  have : IsIntegrallyClosed Γ(f.normalization, V) :=
    generic_normalization_affine_sections_normal Y U hU
  let x : V := ⟨z, hzV⟩
  let : Algebra Γ(f.normalization, V) (f.normalization.presheaf.stalk z) :=
    f.normalization.presheaf.algebra_section_stalk x
  have := hV.isLocalization_stalk x
  exact isIntegrallyClosed_of_isLocalization _ (hV.primeIdealOf x).asIdeal.primeCompl
    (hV.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors

end
end Negativity
