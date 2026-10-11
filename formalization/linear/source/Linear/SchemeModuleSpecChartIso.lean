module
public import Linear.SchemeModuleSpecChartMorphism
import all Linear.SchemeModuleSpecChartMorphism
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
variable {X : Scheme.{u}} {R : CommRingCat.{u}}
variable (M N : X.Modules) (j : Spec R ⟶ X) [IsOpenImmersion j]
variable (U : X.Opens) (hi : j ''ᵁ ⊤ = U) (φ : R ⟶ Γ(X,U))
variable (hφ : φ ≫ j.appLE U ⊤ (by rw [← hi]; exact (j.preimage_image_eq ⊤).ge) = (Scheme.ΓSpecIso R).inv)
variable [(M.restrict j).IsQuasicoherent] [(N.restrict j).IsQuasicoherent]

/-- The actual whole-chart comparison is an isomorphism once BOTH
original restricted sheaves are quasicoherent. This follows from the
proved exact section map and localization; the conclusion is not an input. -/
theorem schemeModuleSpecChartMorphism_isIso
    (C : letI := Module.compHom Γ(M,U) φ.hom
         letI := Module.compHom Γ(N,U) φ.hom
         Γ(M,U) ≃ₗ[R] Γ(N,U)) :
    IsIso (schemeModuleSpecChartMorphism M N j U hi φ hφ C) := by
  letI := Module.compHom Γ(M,U) φ.hom
  letI := Module.compHom Γ(N,U) φ.hom
  let EM := schemeModuleSpecChartSectionsLinearEquiv M j U hi φ hφ
  let EN := schemeModuleSpecChartSectionsLinearEquiv N j U hi φ hφ
  let η := schemeModuleSpecChartMorphism M N j U hi φ hφ C
  have hg : Function.Bijective (moduleSpecΓFunctor.map η).hom := by
    have he : (moduleSpecΓFunctor.map η).hom =
        ((EM.symm.trans C).trans EN).toLinearMap := by
      ext x
      obtain ⟨v,rfl⟩ := EM.surjective x
      exact (schemeModuleSpecChartMorphism_sections M N j U hi φ hφ C v).trans
        (congrArg (fun z => EN (C z)) (EM.symm_apply_apply v).symm)
    rw [he]
    exact ((EM.symm.trans C).trans EN).bijective
  have ht : IsIso ((modulesSpecToSheaf.map η).hom.app (op ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hg
  rw [← isIso_iff_of_reflects_iso η modulesSpecToSheaf]
  exact isLocalizing_of_isIso_app_top ht
    ((isIso_fromTildeΓ_iff_isLocalizing (M.restrict j)).mp inferInstance)
    ((isIso_fromTildeΓ_iff_isLocalizing (N.restrict j)).mp inferInstance)
end LinearStudy
