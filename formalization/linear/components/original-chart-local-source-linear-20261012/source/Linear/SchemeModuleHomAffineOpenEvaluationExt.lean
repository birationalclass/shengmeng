module
public import Linear.AffineQuasicoherentHomActualOpenEvaluation
public import Linear.SchemeModuleHomOpenImmersionBijective
public import Linear.SchemeModuleHomEvaluationRestriction
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

/-- Actual local Hom sections agree on every subopen of an affine
chart once they agree on the RESTRICTIONS of global source sections
of that original chart. This derives the needed gluing extensionality
from source quasicoherence and actual Hom evaluation; it does not
assume that source restriction is surjective or the target is QC. -/
theorem schemeModuleHomAffineOpenSections_evaluation_ext
    (W : (Spec R).Opens)
    (h k : Γ(schemeModuleHomModuleSheaf M N,j ''ᵁ W))
    (he : ∀ x : Γ(M.restrict j,⊤),
      schemeModuleHomSectionEvaluation M N (j ''ᵁ W) h
        ((M.restrict j).presheaf.map W.leTop.op x) =
      schemeModuleHomSectionEvaluation M N (j ''ᵁ W) k
        ((M.restrict j).presheaf.map W.leTop.op x)) : h = k := by
  apply (schemeModuleHomOpenImmersionRestrictSection_bijective M N j W).injective
  apply (affineQuasicoherentHomActualOpenSectionsLinearEquiv (N.restrict j) (M.restrict j) W).injective
  ext x
  rw [affineQuasicoherentHomActualOpenSectionsLinearEquiv_evaluation,
    affineQuasicoherentHomActualOpenSectionsLinearEquiv_evaluation]
  change schemeModuleHomSectionEvaluation M N (j ''ᵁ W) h
      ((M.restrict j).presheaf.map W.leTop.op x) =
    schemeModuleHomSectionEvaluation M N (j ''ᵁ W) k
      ((M.restrict j).presheaf.map W.leTop.op x)
  exact he x
end LinearStudy
