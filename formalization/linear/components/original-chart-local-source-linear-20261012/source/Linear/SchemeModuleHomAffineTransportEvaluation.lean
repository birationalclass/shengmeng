module
public import Linear.SchemeModuleHomCompositeEvaluation
public import Linear.SchemeModuleHomAffineTransportSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
variable (R : CommRingCat.{u}) (e : ↑U ≅ Spec R) {P Q : (Spec R).Modules}

/-- The same transported Hom section has the actual conjugated module
morphism, with the original composite restriction retained. -/
theorem schemeModuleHomAffineTransportSectionsEquiv_morphism_value
    (α : M.restrict (e.inv ≫ U.ι) ≅ P)
    (β : N.restrict (e.inv ≫ U.ι) ≅ Q)
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomTopSectionsEquiv P Q
      (schemeModuleHomAffineTransportSectionsEquiv M N U R e α β h) =
    α.inv ≫ schemeModuleHomCompositeRestriction M N U e.inv h ≫ β.hom := by
  simp only [schemeModuleHomAffineTransportSectionsEquiv,Equiv.trans_apply,
    Equiv.apply_symm_apply,Iso.homCongr_apply]
  exact congrArg (fun k => α.inv ≫ k ≫ β.hom)
    (eq_of_heq (affineCompositeHEq M N U R e h))

/-- On every affine-chart open, the transported Hom evaluates the SAME
original section by actual global Hom restriction and the actual chart isos. -/
theorem schemeModuleHomAffineTransportSectionsEquiv_evaluation
    (α : M.restrict (e.inv ≫ U.ι) ≅ P)
    (β : N.restrict (e.inv ≫ U.ι) ≅ Q)
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) (W : (Spec R).Opens)
    (x : Γ(M,U.ι ''ᵁ (e.inv ''ᵁ W))) :
    let i : U.ι ''ᵁ (e.inv ''ᵁ W) ⟶ U := homOfLE
      ((Scheme.Hom.image_mono U.ι le_top).trans (le_of_eq U.ι_image_top))
    let A := (Scheme.Modules.restrictFunctorComp e.inv U.ι).symm.app M
    let B := (Scheme.Modules.restrictFunctorComp e.inv U.ι).symm.app N
    (schemeModuleHomTopSectionsEquiv P Q
      (schemeModuleHomAffineTransportSectionsEquiv M N U R e α β h)).app W
      (α.hom.app W (A.hom.app W
        (((M.restrict U.ι).restrictAppIso e.inv W).inv
          ((M.restrictAppIso U.ι (e.inv ''ᵁ W)).inv x)))) =
    β.hom.app W (B.hom.app W
      (((N.restrict U.ι).restrictAppIso e.inv W).inv
        ((N.restrictAppIso U.ι (e.inv ''ᵁ W)).inv
          (schemeModuleHomSectionEvaluation M N (U.ι ''ᵁ (e.inv ''ᵁ W))
            ((schemeModuleHomModuleSheaf M N).presheaf.map i.op h) x)))) := by
  dsimp only
  rw [schemeModuleHomAffineTransportSectionsEquiv_morphism_value]
  have H := α.hom_inv_id
  have hx := congrArg (fun k => k.app W
    (((Scheme.Modules.restrictFunctorComp e.inv U.ι).symm.app M).hom.app W
      (((M.restrict U.ι).restrictAppIso e.inv W).inv
        ((M.restrictAppIso U.ι (e.inv ''ᵁ W)).inv x)))) H
  dsimp at hx ⊢
  rw [hx]
  exact congrArg (fun y => β.hom.app W y)
    (schemeModuleHomCompositeRestriction_evaluation M N U e.inv h W x)

end LinearStudy
