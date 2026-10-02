module

public import Negativity.CurveCycleProjection
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Actual scheme-theoretic images of reduced sources are reduced. -/
theorem actual_image_isReduced {C X : Scheme.{u}} [IsReduced C]
    (f : C ⟶ X) [QuasiCompact f] : IsReduced f.image := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro z
  obtain ⟨U, hU, hzU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f.imageι z) trivial
  let V := f.imageι ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f.imageι
  have : _root_.IsReduced Γ(f.image, V) :=
    isReduced_of_injective (f.toImage.app V).hom (f.toImage_app_injective ⟨U, hU⟩)
  let x : V := ⟨z, hzU⟩
  let : Algebra Γ(f.image, V) (f.image.presheaf.stalk z) :=
    f.image.presheaf.algebra_section_stalk x
  have := hV.isLocalization_stalk x
  exact isReduced_localizationPreserves (hV.primeIdealOf x).asIdeal.primeCompl _ inferInstance

/-- A proper map from an integral source has an actual integral image. -/
theorem proper_integral_actual_image_isIntegral {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) [IsProper f] : IsIntegral f.image := by
  have : IsReduced f.image := actual_image_isReduced f
  have : IrreducibleSpace f.image := f.toImage.surjective.irreducibleSpace f.toImage.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Proper images of complete integral curves are integral, complete and
at most one-dimensional actual schemes. The image is constructed, rather
than supplied as an abstract curve with compatibility assumptions. -/
theorem complete_integral_curve_actual_image_properties
    {C X : Scheme.{u}} [IsIntegral C]
    (hdC : Order.krullDim C = 1)
    (k : Type u) [Field k]
    (b : X ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    (f : C ⟶ X) [IsProper (f ≫ b)] :
    IsProper f.toImage ∧ Surjective f.toImage ∧ IsIntegral f.image ∧
      IsProper (f.imageι ≫ b) ∧ Order.krullDim f.image ≤ 1 := by
  have : IsProper f := IsProper.of_comp f b
  have : IsProper f.toImage := by
    have : IsProper (f.toImage ≫ f.imageι) := by simpa
    exact IsProper.of_comp f.toImage f.imageι
  have : Surjective f.toImage := inferInstance
  have : IsIntegral f.image := proper_integral_actual_image_isIntegral f
  have : UniversallyClosed (f.toImage ≫ (f.imageι ≫ b)) := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    infer_instance
  have : UniversallyClosed (f.imageι ≫ b) :=
    UniversallyClosed.of_comp_surjective f.toImage (f.imageι ≫ b)
  have : IsProper (f.imageι ≫ b) := ⟨⟩
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  apply Order.krullDim_le_one_iff.mpr
  intro y
  by_cases hy : y = genericPoint f.image
  · right
    subst y
    exact fun _ _ => (genericPoint_spec f.image).specializes trivial
  · left
    obtain ⟨x, rfl⟩ := f.toImage.surjective y
    have hx : x ≠ genericPoint C := by
      intro he
      exact hy (he ▸ dominant_genericPoint_eq f.toImage)
    have hc := f.toImage.isClosedMap _ (curve_coheight_one_isClosed C hdC.le x
      (curve_nonGeneric_coheight_one C hdC.le x hx))
    rw [Set.image_singleton] at hc
    intro z hz
    have he : z = f.toImage x := Set.mem_singleton_iff.mp
      (hc.closure_eq ▸ hz.mem_closure)
    exact he.symm ▸ le_refl _

end
end Negativity
