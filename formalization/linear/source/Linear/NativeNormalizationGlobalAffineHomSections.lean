module
public import Linear.NativeNormalizationPushforwardStructureChart
public import Linear.SchemeModuleHomAffineChartSections
public import Linear.SchemeModuleHomTopSections
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

/-- The ACTUAL global Hom_O(pi_*O,O) on the SAME original finite
normalization chart has exactly the sections of the verified ACTUAL
affine Hom_O(g_*O,O). This retains original module restrictions and
their chart maps. It is a section equivalence, not global duality. -/
def nativeNormalizationGlobalAffineHomSectionsEquiv
    (a : R) (ha : a ∈ 𝒜 1) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf),Proj.basicOpen 𝒜 a) ≃
    Γ(schemeModuleHomModuleSheaf ((Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤) :=
  (schemeModuleHomAffineChartSectionsEquiv _ _ (Proj.basicOpen 𝒜 a) _
    (Proj.basicOpenIsoSpec 𝒜 a ha (by decide))).trans
    ((Iso.homCongr (nativeNormalizationPushforwardStructureChartModuleIso 𝒜 𝓑 a ha)
      (Scheme.Modules.restrictUnitIso (Proj.awayι 𝒜 a ha (by decide)))).trans
      (schemeModuleHomTopSectionsEquiv _ _).symm)

end LinearStudy
