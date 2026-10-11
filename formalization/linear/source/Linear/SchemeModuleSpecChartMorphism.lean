module
public import Linear.AffineQuasicoherentSourceMorphismsSections
public import Linear.SchemeModuleSpecChartSectionsLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {R : CommRingCat.{u}}
variable (M N : X.Modules) (j : Spec R ⟶ X) [IsOpenImmersion j]
variable (U : X.Opens) (hi : j ''ᵁ ⊤ = U) (φ : R ⟶ Γ(X,U))
variable (hφ : φ ≫ j.appLE U ⊤ (by rw [← hi]; exact (j.preimage_image_eq ⊤).ge) = (Scheme.ΓSpecIso R).inv)
variable [(M.restrict j).IsQuasicoherent]

/-- Any given original chart-section linear map extends to the whole
actual affine chart through the real tilde adjunction. The chart and
scalar pullback are retained, with no target quasicoherence premise. -/
def schemeModuleSpecChartMorphism
    (C : letI := Module.compHom Γ(M,U) φ.hom
         letI := Module.compHom Γ(N,U) φ.hom
         Γ(M,U) ≃ₗ[R] Γ(N,U)) : M.restrict j ⟶ N.restrict j := by
  letI := Module.compHom Γ(M,U) φ.hom
  letI := Module.compHom Γ(N,U) φ.hom
  let EM := schemeModuleSpecChartSectionsLinearEquiv M j U hi φ hφ
  let EN := schemeModuleSpecChartSectionsLinearEquiv N j U hi φ hφ
  let f : moduleSpecΓFunctor.obj (M.restrict j) →ₗ[R] moduleSpecΓFunctor.obj (N.restrict j) :=
    ((EM.symm.trans C).trans EN).toLinearMap
  exact (affineQuasicoherentSourceMorphismsEquiv (M.restrict j) (N.restrict j)).symm
    ((ModuleCat.homEquiv
      (M := moduleSpecΓFunctor.obj (M.restrict j))
      (N := moduleSpecΓFunctor.obj (N.restrict j))).symm f)

/-- The actual extension has exactly the original linear map on chart
sections after the actual Spec-chart scalar transport. -/
theorem schemeModuleSpecChartMorphism_sections
    (C : letI := Module.compHom Γ(M,U) φ.hom
         letI := Module.compHom Γ(N,U) φ.hom
         Γ(M,U) ≃ₗ[R] Γ(N,U)) (v : Γ(M,U)) :
    (moduleSpecΓFunctor.map (schemeModuleSpecChartMorphism M N j U hi φ hφ C)).hom
      (schemeModuleSpecChartSectionsLinearEquiv M j U hi φ hφ v) =
    schemeModuleSpecChartSectionsLinearEquiv N j U hi φ hφ (C v) := by
  letI := Module.compHom Γ(M,U) φ.hom
  letI := Module.compHom Γ(N,U) φ.hom
  let EM := schemeModuleSpecChartSectionsLinearEquiv M j U hi φ hφ
  let EN := schemeModuleSpecChartSectionsLinearEquiv N j U hi φ hφ
  rw [schemeModuleSpecChartMorphism,affineQuasicoherentSourceMorphismsEquiv_symm_map]
  exact congrArg (fun z => EN (C z)) (EM.symm_apply_apply v)
end LinearStudy
