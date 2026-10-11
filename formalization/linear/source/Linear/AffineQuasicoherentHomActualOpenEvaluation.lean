module
public import Linear.AffineQuasicoherentHomActualOpenSections
public import Linear.SchemeModuleHomOpenEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : CommRingCat.{u}} (M N : (Spec R).Modules) [M.IsQuasicoherent]

/-- The actual affine open Hom equivalence evaluates the original
section h on the actual restriction of the original global source x. -/
theorem affineQuasicoherentHomActualOpenSectionsLinearEquiv_evaluation
    (U : (Spec R).Opens) (h : Γ(schemeModuleHomModuleSheaf M N,U))
    (x : Γ(M,⊤)) :
    affineQuasicoherentHomActualOpenSectionsLinearEquiv N M U h x =
      schemeModuleHomSectionEvaluation M N U h (M.presheaf.map U.leTop.op x) := by
  let V : (Spec R).Opens := U.ι ''ᵁ ⊤
  let i : op V ⟶ op U := (eqToHom U.ι_image_top.symm).op
  let k : V ⟶ U := homOfLE (by simpa only [V,U.ι_image_top] using le_refl U)
  let x0 : (moduleSpecΓFunctor (R := R)).obj M := x
  change affineOpenPushforwardSectionsLinearEquiv N U
    (affineQuasicoherentHomOpenSectionsEquiv M N U h x0) = _
  rw [affineQuasicoherentHomOpenSectionsEquiv_evaluation]
  change N.presheaf.map i ((schemeModuleHomOpenSectionsEquiv M N U h).app ⊤
    ((M.restrictAppIso U.ι ⊤).inv (M.presheaf.map V.leTop.op x))) = _
  rw [schemeModuleHomOpenSectionsEquiv_evaluation]
  change N.presheaf.map i
    (schemeModuleHomSectionEvaluation M N V
      ((schemeModuleHomModuleSheaf M N).presheaf.map k.op h)
      (M.presheaf.map V.leTop.op x)) = _
  have H := schemeModuleHomSectionEvaluation_restrict M N i.unop
    ((schemeModuleHomModuleSheaf M N).presheaf.map k.op h)
    (M.presheaf.map V.leTop.op x)
  have hh : (schemeModuleHomModuleSheaf M N).presheaf.map i
      ((schemeModuleHomModuleSheaf M N).presheaf.map k.op h) = h := by
    change ((schemeModuleHomModuleSheaf M N).presheaf.map k.op ≫
      (schemeModuleHomModuleSheaf M N).presheaf.map i) h = h
    rw [← Functor.map_comp, show k.op ≫ i = 𝟙 (op U) from Subsingleton.elim _ _,CategoryTheory.Functor.map_id]
    rfl
  have hx : M.presheaf.map i (M.presheaf.map V.leTop.op x) = M.presheaf.map U.leTop.op x := by
    change (M.presheaf.map V.leTop.op ≫ M.presheaf.map i) x = _
    rw [← Functor.map_comp, show V.leTop.op ≫ i = U.leTop.op from Subsingleton.elim _ _]
  simp only [Quiver.Hom.op_unop,hh,hx] at H
  exact H.symm

/-- On every inclusion, restriction of actual Hom sections corresponds
to localization of the target alone, retaining the same global source. -/
theorem affineQuasicoherentHomActualOpenSectionsLinearEquiv_restrict
    {U V : (Spec R).Opens} (i : V ⟶ U)
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) (x : Γ(M,⊤)) :
    affineQuasicoherentHomActualOpenSectionsLinearEquiv N M V
      ((schemeModuleHomModuleSheaf M N).presheaf.map i.op h) x =
    N.presheaf.map i.op
      (affineQuasicoherentHomActualOpenSectionsLinearEquiv N M U h x) := by
  rw [affineQuasicoherentHomActualOpenSectionsLinearEquiv_evaluation,
    affineQuasicoherentHomActualOpenSectionsLinearEquiv_evaluation]
  have H := schemeModuleHomSectionEvaluation_restrict M N i h
    (M.presheaf.map U.leTop.op x)
  have hx : M.presheaf.map i.op (M.presheaf.map U.leTop.op x) = M.presheaf.map V.leTop.op x := by
    change (M.presheaf.map U.leTop.op ≫ M.presheaf.map i.op) x = _
    rw [← Functor.map_comp,show U.leTop.op ≫ i.op = V.leTop.op from Subsingleton.elim _ _]
  rw [hx] at H
  exact H
end LinearStudy
