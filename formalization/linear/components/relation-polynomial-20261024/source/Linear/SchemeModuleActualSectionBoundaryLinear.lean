module
public import Linear.SchemeModuleActualSectionBoundaryScalar
public import Linear.SchemeModuleActualHSpecScalars
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
/-- ORIGINAL sections acquire their base-field action through the actual
scheme structure map and canonical GammaSpecIso,independently of any
Ext,duality or boundary comparison. -/
def schemeModuleSectionsSpecModule {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (E : X.Modules) : Module K Γ(E,⊤) :=
  Module.compHom Γ(E,⊤) (pi.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
/-- Exact original base-field multiplication on ORIGINAL sections. -/
theorem schemeModuleSectionsSpecModule_smul {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (E : X.Modules) (a : K) (s : Γ(E,⊤)) :
    letI := schemeModuleSectionsSpecModule pi E
    a • s = pi.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) • s := rfl
/-- The SAME original Ext-class actual section boundary as a base-field
linear map. Linearity is derived from original global scalar centrality,
not assumed or transported via a duality isomorphism. -/
def schemeModuleExtClassActualSectionBoundarySpecLinearMap
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) {E M : X.Modules} (r : ℕ) (epsilon : Ext.{u} E M r) :
    letI : Module K Γ(E,⊤) := schemeModuleSectionsSpecModule pi E
    letI : Module K (schemeModuleActualCohomology X M r) := schemeModuleActualHSpecModule pi M r
    Γ(E,⊤) →ₗ[K] schemeModuleActualCohomology X M r := by
  letI : Module K Γ(E,⊤) := schemeModuleSectionsSpecModule pi E
  letI : Module K (schemeModuleActualCohomology X M r) := schemeModuleActualHSpecModule pi M r
  exact {
    __ := schemeModuleExtClassActualSectionBoundaryAddHom epsilon
    map_smul' := fun a s => schemeModuleExtClassActualSectionBoundary_originalScalar X r epsilon
      (pi.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) s }
/-- Forgetting this verified linearity returns EXACTLY the old actual
section boundary additive map,not an isomorphic replacement. -/
theorem schemeModuleExtClassActualSectionBoundarySpecLinearMap_forget
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) {E M : X.Modules} (r : ℕ) (epsilon : Ext.{u} E M r) :
    letI : Module K Γ(E,⊤) := schemeModuleSectionsSpecModule pi E
    letI : Module K (schemeModuleActualCohomology X M r) := schemeModuleActualHSpecModule pi M r
    (show Γ(E,⊤) →ₗ[K] schemeModuleActualCohomology X M r from
      schemeModuleExtClassActualSectionBoundarySpecLinearMap pi r epsilon).toAddMonoidHom =
        schemeModuleExtClassActualSectionBoundaryAddHom epsilon := rfl
/-- Specialize to the SAME ORIGINAL chain/Koszul roof,augmentation,
quasi-isomorphism,above-top vanishing and top coefficient identification.
No desired linearity or replacement Ext class is input. -/
def schemeModuleOriginalActualSectionBoundarySpecLinearMap
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) {E M : X.Modules}
    (CC : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : CC ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (CC.X (r+1))) (phi : CC.X r ≅ M) :
    letI : Module K Γ(E,⊤) := schemeModuleSectionsSpecModule pi E
    letI : Module K (schemeModuleActualCohomology X M r) := schemeModuleActualHSpecModule pi M r
    Γ(E,⊤) →ₗ[K] schemeModuleActualCohomology X M r :=
  schemeModuleExtClassActualSectionBoundarySpecLinearMap pi r
    (schemeModuleOriginalChainTopExtClassSmall CC r alpha hAlpha phi.hom (hAbove.eq_of_src _ _))
/-- The underlying map is EXACTLY the SAME original actual boundary. -/
theorem schemeModuleOriginalActualSectionBoundarySpecLinearMap_forget
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) {E M : X.Modules}
    (CC : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : CC ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (CC.X (r+1))) (phi : CC.X r ≅ M) :
    letI : Module K Γ(E,⊤) := schemeModuleSectionsSpecModule pi E
    letI : Module K (schemeModuleActualCohomology X M r) := schemeModuleActualHSpecModule pi M r
    (show Γ(E,⊤) →ₗ[K] schemeModuleActualCohomology X M r from
      schemeModuleOriginalActualSectionBoundarySpecLinearMap pi CC r alpha hAlpha hAbove phi).toAddMonoidHom =
        schemeModuleOriginalActualSectionBoundary CC r alpha hAlpha hAbove phi := rfl
end LinearStudy
