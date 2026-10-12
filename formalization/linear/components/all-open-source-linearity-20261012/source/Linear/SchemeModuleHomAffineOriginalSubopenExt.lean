module
public import Linear.SchemeModuleHomAffineOpenEvaluationExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 650000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} {R : CommRingCat.{u}}
variable (M N : X.Modules) (j : Spec R ⟶ X) [IsOpenImmersion j]
variable [(M.restrict j).IsQuasicoherent]

/-- On every ORIGINAL subopen V of the actual affine chart U, the
restriction-evaluation test determines the entire Hom section.
Original image and inclusion maps are derived, not certificate inputs. -/
theorem schemeModuleHomAffineOriginalSubopen_evaluation_ext
    (U : X.Opens) (hi : j ''ᵁ ⊤ = U) (V : X.Opens) (hle : V ≤ U)
    (h k : Γ(schemeModuleHomModuleSheaf M N,V))
    (he : ∀ x : Γ(M,U),
      schemeModuleHomSectionEvaluation M N V h (M.presheaf.map (homOfLE hle).op x) =
      schemeModuleHomSectionEvaluation M N V k (M.presheaf.map (homOfLE hle).op x)) : h = k := by
  subst U
  let W := j ⁻¹ᵁ V
  have himg : j ''ᵁ W = V := by
    rw [j.image_preimage_eq_opensRange_inf,inf_eq_right]
    simpa only [j.image_top_eq_opensRange] using hle
  have aux (V' : X.Opens) (hV' : j ''ᵁ W = V') (hle' : V' ≤ j ''ᵁ ⊤)
      (h' k' : Γ(schemeModuleHomModuleSheaf M N,V'))
      (he' : ∀ x : Γ(M,j ''ᵁ ⊤),
        schemeModuleHomSectionEvaluation M N V' h' (M.presheaf.map (homOfLE hle').op x) =
        schemeModuleHomSectionEvaluation M N V' k' (M.presheaf.map (homOfLE hle').op x)) : h' = k' := by
    subst V'
    apply schemeModuleHomAffineOpenSections_evaluation_ext M N j W
    intro x
    exact he' x
  exact aux V himg hle h k he
end LinearStudy
