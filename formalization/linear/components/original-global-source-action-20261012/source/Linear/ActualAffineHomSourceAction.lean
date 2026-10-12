module
public import Linear.PushforwardHomSourceActionModule
public import Linear.ActualAffineAlgebraDualEvaluationExt
public import Linear.ActualAffineStructureElementValue
public import Linear.NativeCoextensionLocalizationUpper
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 120000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u

/-- Evaluation of the actual source action on its original open. -/
theorem schemePushforwardHomSourceActionSection_original_evaluation
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    (b x : Γ(X,f ⁻¹ᵁ U))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    schemeModuleHomSectionEvaluation _ N U
      (schemePushforwardHomSourceActionSection f N U b h) x =
    schemeModuleHomSectionEvaluation _ N U h (b*x) := by
  change h.val.app (op (Over.mk (𝟙 U)))
    (X.presheaf.map ((Opens.map f.base).map (𝟙 U)).op b * x) = _
  have hm : X.presheaf.map ((Opens.map f.base).map (𝟙 U)).op = 𝟙 _ := by
    simp only [CategoryTheory.Functor.map_id,op_id]
  erw [hm]
  rfl

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Original algebra elements map multiplicatively to actual source sections. -/
theorem actualAffineAlgebraStructurePushforwardIso_element_mul (b x : B) :
    (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
      (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ (b*x)) =
    (show Γ(Spec (CommRingCat.of B),
       Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ ⊤) from
      (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
        (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ b)) *
    (show Γ(Spec (CommRingCat.of B),
       Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ ⊤) from
      (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
        (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ x)) := by
  have H (a : B) := eq_of_heq
    (actualAffineAlgebraStructurePushforwardIso_element_value (A := A) a)
  rw [H (b*x),H b,H x]
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b x

end LinearStudy
