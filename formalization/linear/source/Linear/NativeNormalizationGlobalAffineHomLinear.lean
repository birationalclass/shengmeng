module
public import Linear.SchemeModuleHomAffineTransportLinear
public import Linear.NativeNormalizationGlobalAffineHomSections
public import Linear.OriginalProjectiveChartScalarTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
/-- The original global Hom chart has its original degree-zero base-ring scalar action. -/
@[instance_reducible] def nativeNormalizationGlobalHomChartModule
    (a : R) (ha : a ∈ 𝒜 1) :=
  schemeModuleHomChartBaseModule
    ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf) (Proj.basicOpen 𝒜 a)
    (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a)) (Proj.awayToSection 𝒜 a).hom
/-- Actual ORIGINAL global-to-affine internal Hom SECTION LINEAR equivalence.
The original chart scalar square and actual module-chart isomorphisms are proved, not assumed.
This chart equivalence does not assert global finite duality or canonical identification. -/
def nativeNormalizationGlobalAffineHomSectionsLinearEquiv
    (a : R) (ha : a ∈ 𝒜 1) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let P := (Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
    letI := originalAffineHomBaseModule (CommRingCat.of A) P Q
    Γ(schemeModuleHomModuleSheaf M N,Proj.basicOpen 𝒜 a) ≃ₗ[A]
      Γ(schemeModuleHomModuleSheaf P Q,⊤) := by
  dsimp only
  exact schemeModuleHomAffineTransportSectionsLinearEquiv _ _ (Proj.basicOpen 𝒜 a)
    (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))
    (Proj.basicOpenIsoSpec 𝒜 a ha (by decide)) (Proj.awayToSection 𝒜 a).hom
    (fun c => congr($(originalProjectiveChartScalarTransport 𝒜 a ha) c))
    (nativeNormalizationPushforwardStructureChartModuleIso 𝒜 𝓑 a ha)
    (Scheme.Modules.restrictUnitIso (Proj.awayι 𝒜 a ha (by decide)))
/-- The constructed linear equivalence is EXACTLY the old specified original section equivalence. -/
theorem nativeNormalizationGlobalAffineHomSectionsLinearEquiv_toEquiv
    (a : R) (ha : a ∈ 𝒜 1) :
    (nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha).toEquiv =
      nativeNormalizationGlobalAffineHomSectionsEquiv 𝒜 𝓑 a ha := by
  rfl
end LinearStudy
