module
public import Linear.SchemeModuleHomAffineTransportEvaluation
public import Linear.ActualAffineAlgebraDualEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
variable (R : CommRingCat.{u}) (e : ↑U ≅ Spec R) {P Q : (Spec R).Modules}
theorem schemeModuleHomAffineTransportSectionsEquiv_transported_evaluation
    (α : M.restrict (e.inv ≫ U.ι) ≅ P)
    (β : N.restrict (e.inv ≫ U.ι) ≅ Q)
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) (W : (Spec R).Opens)
    (x : Γ(M.restrict (e.inv ≫ U.ι),W)) :
    schemeModuleHomSectionEvaluation P Q W
      ((schemeModuleHomModuleSheaf P Q).presheaf.map (homOfLE le_top).op
        (schemeModuleHomAffineTransportSectionsEquiv M N U R e α β h))
      (α.hom.app W x) =
    β.hom.app W ((schemeModuleHomCompositeRestriction M N U e.inv h).app W x) := by
  change (schemeModuleHomTopSectionsEquiv P Q
    (schemeModuleHomAffineTransportSectionsEquiv M N U R e α β h)).app W
      (α.hom.app W x) = _
  rw [schemeModuleHomAffineTransportSectionsEquiv_morphism_value]
  have hx := congrArg (fun k => k.app W x) α.hom_inv_id
  dsimp at hx ⊢
  rw [hx]
theorem schemeModuleHomAffineTransportSectionsEquiv_top_transported_evaluation
    (α : M.restrict (e.inv ≫ U.ι) ≅ P)
    (β : N.restrict (e.inv ≫ U.ι) ≅ Q)
    (h : Γ(schemeModuleHomModuleSheaf M N,U))
    (x : Γ(M.restrict (e.inv ≫ U.ι),⊤)) :
    schemeModuleHomSectionEvaluation P Q ⊤
      (schemeModuleHomAffineTransportSectionsEquiv M N U R e α β h)
      (α.hom.app ⊤ x) =
    β.hom.app ⊤ ((schemeModuleHomCompositeRestriction M N U e.inv h).app ⊤ x) := by
  change (schemeModuleHomTopSectionsEquiv P Q
    (schemeModuleHomAffineTransportSectionsEquiv M N U R e α β h)).app ⊤
      (α.hom.app ⊤ x) = _
  rw [schemeModuleHomAffineTransportSectionsEquiv_morphism_value]
  have hx := congrArg (fun k => k.app ⊤ x) α.hom_inv_id
  dsimp at hx ⊢
  rw [hx]
end LinearStudy
