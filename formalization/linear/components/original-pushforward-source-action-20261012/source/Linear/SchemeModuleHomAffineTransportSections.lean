module
public import Linear.AffineHomScalarHEq
public import Linear.SchemeModuleHomAffineDirectAdd
public import Linear.SchemeModuleHomTopScalars
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
variable (R : CommRingCat.{u}) (e : ↑U ≅ Spec R) {P Q : (Spec R).Modules}
/-- The original affine Hom equivalence, followed by actual module-chart isomorphisms. -/
def schemeModuleHomAffineTransportSectionsEquiv
    (α : M.restrict (e.inv ≫ U.ι) ≅ P)
    (β : N.restrict (e.inv ≫ U.ι) ≅ Q) :
    Γ(schemeModuleHomModuleSheaf M N,U) ≃ Γ(schemeModuleHomModuleSheaf P Q,⊤) :=
  (schemeModuleHomAffineChartSectionsEquiv M N U R e).trans
    ((Iso.homCongr α β).trans (schemeModuleHomTopSectionsEquiv P Q).symm)
theorem schemeModuleHomAffineTransportSectionsEquiv_smul
    (α : M.restrict (e.inv ≫ U.ι) ≅ P)
    (β : N.restrict (e.inv ≫ U.ι) ≅ Q)
    (r : Γ(X,U)) (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomAffineTransportSectionsEquiv M N U R e α β (r • h) =
      e.inv.appTop (U.topIso.inv r) •
        schemeModuleHomAffineTransportSectionsEquiv M N U R e α β h := by
  apply (schemeModuleHomTopSectionsEquiv P Q).injective
  simp only [schemeModuleHomAffineTransportSectionsEquiv,Equiv.trans_apply,
    Equiv.apply_symm_apply,schemeModuleHomTopSectionsEquiv_smul,Iso.homCongr_apply]
  have hs := eq_of_heq (affineHomScalarHEq M N U R e r h)
  have hi := eq_of_heq (affineCompositeHEq M N U R e h)
  rw [hs]
  unfold affineHomScaledTransport affineHomScalarEnd
  rw [← hi]
  have hn := originalGlobalModuleScalar_naturality (X := Spec R)
    (e.inv.appTop (U.topIso.inv r)) β.hom
  simpa only [Category.assoc] using congrArg
    (fun z => α.inv ≫ schemeModuleHomAffineChartSectionsEquiv M N U R e h ≫ z) hn
theorem schemeModuleHomAffineTransportSectionsEquiv_add
    (α : M.restrict (e.inv ≫ U.ι) ≅ P)
    (β : N.restrict (e.inv ≫ U.ι) ≅ Q)
    (h k : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomAffineTransportSectionsEquiv M N U R e α β (h+k) =
      schemeModuleHomAffineTransportSectionsEquiv M N U R e α β h +
        schemeModuleHomAffineTransportSectionsEquiv M N U R e α β k := by
  apply (schemeModuleHomTopSectionsEquiv P Q).injective
  simp only [schemeModuleHomAffineTransportSectionsEquiv,Equiv.trans_apply,
    Equiv.apply_symm_apply,schemeModuleHomTopSectionsEquiv_add,Iso.homCongr_apply]
  rw [schemeModuleHomAffineChartSectionsEquiv_direct_add]
  simp only [Preadditive.comp_add,Preadditive.add_comp]
end LinearStudy
