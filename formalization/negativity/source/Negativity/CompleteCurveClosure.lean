module

public import Negativity.FunctionFieldDimension
public import Negativity.CurveImageGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem dominant_functionField_constants_comp
    {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (f : C ⟶ Y) [IsDominant f] (k : Type u) [Field k]
    (b : Y ⟶ Spec (.of k)) :
    (dominantFunctionFieldMap f).comp (curveFunctionFieldBaseMap Y k b) =
      curveFunctionFieldBaseMap C k (f ≫ b) := by
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom ((dominantFunctionFieldMap f).comp
    (curveFunctionFieldBaseMap Y k b))) =
    Spec.map (CommRingCat.ofHom (curveFunctionFieldBaseMap C k (f ≫ b)))
  rw [CommRingCat.ofHom_comp, Spec.map_comp,
    curveFunctionFieldBaseMap_spec, curveFunctionFieldBaseMap_spec]
  change Spec.map ((Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv ≫
    f.stalkMap (genericPoint C)) ≫ _ = _
  simp only [Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_inv,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]

theorem quasiCompact_integral_actual_image_isIntegral
    {C X : Scheme.{u}} [IsIntegral C] (f : C ⟶ X) [QuasiCompact f] :
    IsIntegral f.image := by
  have : IsReduced f.image := actual_image_isReduced f
  have : IrreducibleSpace f.image := by
    apply (irreducibleSpace_def _).mpr
    have h := ((IrreducibleSpace.isIrreducible_univ C).image f.toImage
      f.toImage.continuous.continuousOn).closure
    simpa only [Set.image_univ, f.toImage.denseRange.closure_range, Set.top_eq_univ] using h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Final theorem: the actual scheme-theoretic closure of an immersed
integral affine curve in a complete variety is a complete integral curve.
The dimension of the boundary is controlled by the actual function field,
not by an assumed statement that a closure remains a curve. -/
theorem complete_integral_curve_actual_closure
    {C X : Scheme.{u}} [IsIntegral C]
    (hdC : Order.krullDim C = 1) (k : Type u) [Field k]
    (b : X ⟶ Spec (.of k)) [IsProper b]
    (f : C ⟶ X) [IsImmersion f] [QuasiCompact f] :
    IsIntegral f.image ∧ Order.krullDim f.image = 1 ∧
      IsProper (f.imageι ≫ b) ∧ IsOpenImmersion f.toImage := by
  have : IsIntegral f.image := quasiCompact_integral_actual_image_isIntegral f
  let : Algebra k f.image.functionField :=
    (curveFunctionFieldBaseMap f.image k (f.imageι ≫ b)).toAlgebra
  let : Algebra k C.functionField :=
    (curveFunctionFieldBaseMap C k (f ≫ b)).toAlgebra
  have hconst : (dominantFunctionFieldMap f.toImage).comp
      (curveFunctionFieldBaseMap f.image k (f.imageι ≫ b)) =
      curveFunctionFieldBaseMap C k (f ≫ b) := by
    simpa only [← Category.assoc, Scheme.Hom.toImage_imageι] using
      dominant_functionField_constants_comp f.toImage k (f.imageι ≫ b)
  let φ : f.image.functionField →ₐ[k] C.functionField :=
    { __ := dominantFunctionFieldMap f.toImage
      commutes' := fun a => DFunLike.congr_fun hconst a }
  obtain ⟨x, hx⟩ := curve_exists_coheight_one C hdC
  have htr := (curve_functionField_properties_of_closed_point C hdC.le x hx k
    (f ≫ b) rfl).2
  have hletr : Algebra.trdeg k f.image.functionField ≤ 1 := by
    simpa only [htr] using trdeg_le_of_injective φ φ.injective
  have hdim := integral_scheme_dimension_of_functionField_trdeg_le_one
    f.image k (f.imageι ≫ b) rfl hletr
  have hmono : StrictMono f.toImage := by
    intro a c hac
    refine ⟨f.toImage.continuous.specialization_monotone hac.le, ?_⟩
    intro hca
    exact hac.not_ge (f.toImage.isOpenEmbedding.isEmbedding.isInducing.specializes_iff.mp hca)
  have hdimge := Order.krullDim_le_of_strictMono f.toImage hmono
  rw [hdC] at hdimge
  exact ⟨inferInstance, le_antisymm hdim hdimge, inferInstance, inferInstance⟩

end
end Negativity
