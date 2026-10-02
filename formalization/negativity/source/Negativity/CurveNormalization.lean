module

public import Negativity.GenericNormalizationBirational
public import Negativity.FiniteNormalGeometry
public import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem generic_normalization_dimension_le_one
    (Y : Scheme.{u}) [IsIntegral Y] (hd : Order.krullDim Y ≤ 1) :
    Order.krullDim (Y.fromSpecStalk (genericPoint Y)).normalization ≤ 1 := by
  let f := Y.fromSpecStalk (genericPoint Y)
  rw [Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro z
  obtain ⟨U, hU, hyU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f.fromNormalization z) trivial
  have : Nonempty U := ⟨⟨f.fromNormalization z, hyU⟩⟩
  have hη : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
      (by simpa using ‹Nonempty U›)
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨IsLocalRing.closedPoint Y.functionField,
    by simpa [f] using hη⟩⟩
  let A := Γ(Y, U)
  have : Ring.KrullDimLE 1 A := curve_affine_chart_dimension Y hd U hU
  have : Ring.DimensionLEOne A := ⟨fun {p} hp hprime =>
    hprime.isMaximal_of_ne_bot hp⟩
  let : Algebra A Γ(Spec Y.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Ring.DimensionLEOne (integralClosure A Γ(Spec Y.functionField, f ⁻¹ᵁ U)) :=
    inferInstance
  let V := f.fromNormalization ⁻¹ᵁ U
  have hzV : z ∈ V := hyU
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have hV : IsAffineOpen V := hU.preimage f.fromNormalization
  let e := RingEquiv.ofBijective (f.normalizationObjIso hU).hom.hom
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).hom)
  have : Ring.DimensionLEOne Γ(f.normalization, V) := Ring.DimensionLEOne.of_ringEquiv e
  let x : V := ⟨z, hzV⟩
  let : Algebra Γ(f.normalization, V) (f.normalization.presheaf.stalk z) :=
    f.normalization.presheaf.algebra_section_stalk x
  have := hV.isLocalization_stalk x
  have : Ring.DimensionLEOne (f.normalization.presheaf.stalk z) :=
    Ring.DimensionLEOne.localization _ (hV.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors
  have : Ring.KrullDimLE 1 (f.normalization.presheaf.stalk z) := inferInstance
  rw [← ringKrullDim_stalk_eq_coheight z]
  exact Ring.krullDimLE_iff.mp inferInstance

theorem finiteType_perfectField_normalization_surjective
    (Y : Scheme.{u}) [IsIntegral Y] (k : Type u) [Field k] [PerfectField k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b] :
    Surjective (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  let f := Y.fromSpecStalk (genericPoint Y)
  have : IsFinite f.fromNormalization := finiteType_perfectField_normalization_isFinite Y k b
  have : IsDominant f := generic_stalk_dominant Y
  have : IsDominant f.fromNormalization := by
    have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
      rw [f.toNormalization_fromNormalization]
      infer_instance
    exact IsDominant.of_comp f.toNormalization f.fromNormalization
  exact surjective_of_isDominant_of_isClosed_range f.fromNormalization
    (f.fromNormalization.isClosedMap.isClosed_range)

/-- Final theorem: an actual complete integral curve has a finite,
surjective, birational normalization which is a complete normal integral
curve of dimension one. No normality, finite normalization, or curve
dimension of the normalization is supplied as an input. -/
theorem complete_integral_curve_normalization_properties
    (Y : Scheme.{u}) [IsIntegral Y] (hd : Order.krullDim Y = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [IsProper b] :
    let f := Y.fromSpecStalk (genericPoint Y)
    IsFinite f.fromNormalization ∧ BirationalMorphism f.fromNormalization ∧
      Surjective f.fromNormalization ∧
      (∀ z : f.normalization, IsIntegrallyClosed (f.normalization.presheaf.stalk z)) ∧
      Order.krullDim f.normalization = 1 ∧ IsLocallyNoetherian f.normalization ∧
      IsProper (f.fromNormalization ≫ b) := by
  let f := Y.fromSpecStalk (genericPoint Y)
  have hfin : IsFinite f.fromNormalization := finiteType_perfectField_normalization_isFinite Y k b
  have hbir := finiteType_perfectField_normalization_birational Y k b
  have hsur := finiteType_perfectField_normalization_surjective Y k b
  have hn := generic_normalization_stalks_normal Y
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian b
  have : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  have hdle := generic_normalization_dimension_le_one Y hd.le
  have hdge : 1 ≤ Order.krullDim f.normalization := by
    have := birationalMorphism_dominant f.fromNormalization hbir
    obtain ⟨y, hy⟩ := curve_exists_coheight_one Y hd
    obtain ⟨z, hz⟩ := hsur.surj y
    change f.fromNormalization z = y at hz
    have hznt : z ≠ genericPoint f.normalization := by
      intro he
      rw [he] at hz
      have hη := dominant_genericPoint_eq f.fromNormalization
      have hytop : y = genericPoint Y := hz.symm.trans hη
      rw [hytop] at hy
      have hzero : Order.coheight (genericPoint Y) = 0 := Order.coheight_top Y
      rw [hzero] at hy
      norm_num at hy
    have hzlt : z < (⊤ : f.normalization) := lt_iff_le_not_ge.mpr
      ⟨le_top, fun h => hznt (Specializes.antisymm h (genericPoint_specializes z)).eq⟩
    have hp : 0 < Order.coheight z := Order.coheight_pos_of_lt_top hzlt
    exact le_trans (by exact_mod_cast Order.one_le_iff_pos.mpr hp)
      (Order.coheight_le_krullDim z)
  exact ⟨hfin, hbir, hsur, hn, le_antisymm hdle hdge, inferInstance, inferInstance⟩

end
end Negativity
