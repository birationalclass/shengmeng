module
public import Linear.SchemeModuleHomModuleSheaf
public import Mathlib.CategoryTheory.Equivalence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} (M N : X.Modules)
variable (j : Y ⟶ X) [IsOpenImmersion j]

/-- Every subopen of the actual image of W is the image of a unique
subopen of W. This derives the slice equivalence from the original open
immersion, without an assumed Hom comparison. -/
theorem openImmersionOverPost_isEquivalence (W : Y.Opens) :
    (Over.post (X := W) j.opensFunctor).IsEquivalence := by
  let F := Over.post (X := W) j.opensFunctor
  letI : F.EssSurj := {
    mem_essImage Z := by
      let V := j ⁻¹ᵁ Z.left
      have hV : V ≤ W := by
        exact (j.preimage_mono (leOfHom Z.hom)).trans (j.preimage_image_eq W).le
      have hZ : j ''ᵁ V = Z.left := by
        exact (j.image_preimage_eq_opensRange_inf Z.left).trans
          (inf_eq_right.mpr ((leOfHom Z.hom).trans (j.image_le_opensRange W)))
      exact ⟨Over.mk (homOfLE hV), ⟨Over.isoMk (eqToIso hZ)⟩⟩ }
  exact Functor.IsEquivalence.mk inferInstance inferInstance inferInstance

/-- Actual local O-linear maps restrict along the given open immersion
by the original image functor on every subopen. -/
def schemeModuleHomOpenImmersionRestrictSection (W : Y.Opens)
    (h : Γ(schemeModuleHomModuleSheaf M N,j ''ᵁ W)) :
    Γ(schemeModuleHomModuleSheaf (M.restrict j) (N.restrict j),W) :=
  ⟨Functor.whiskerLeft (Over.post (X := W) j.opensFunctor).op h.val,
    fun Z r x => h.property ((Over.post (X := W) j.opensFunctor).op.obj Z)
      ((j.appIso Z.unop.left).inv r) x⟩

/-- This is the actual restriction evaluation, retaining original
sections and the original opens image on both sides. -/
theorem schemeModuleHomOpenImmersionRestrictSection_evaluation
    (W : Y.Opens) (h : Γ(schemeModuleHomModuleSheaf M N,j ''ᵁ W))
    (Z : (Over W)ᵒᵖ) (x : Γ(M.restrict j,Z.unop.left)) :
    (schemeModuleHomOpenImmersionRestrictSection M N j W h).val.app Z x =
      h.val.app ((Over.post (X := W) j.opensFunctor).op.obj Z) x := rfl
end LinearStudy
