module
public import Linear.NativeStructureModuleFraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- Recover the unique native homogeneous local-ring value of an
actual degree-zero module section using its proved local-fraction property. -/
def nativeZeroModuleStructureValue {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (f : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1)
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑) 0).pred f) (p : U) :
    HomogeneousLocalization.AtPrime 𝓑 p.1.asHomogeneousIdeal.toIdeal :=
  (nativeZeroModuleLocalFraction_value_in_structure_image 𝓑 hf p).choose

theorem nativeZeroModuleStructureValue_spec {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (f : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1)
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑) 0).pred f) (p : U) :
    nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1
      (nativeZeroModuleStructureValue 𝓑 f hf p) = f p :=
  (nativeZeroModuleLocalFraction_value_in_structure_image 𝓑 hf p).choose_spec

/-- Recovering native local-ring values preserves the ACTUAL structure
sheaf's locally homogeneous-fraction condition, not only pointwise values. -/
theorem nativeZeroModuleStructureValue_localFraction
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (f : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1)
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑) 0).pred f) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝓑).pred
      (nativeZeroModuleStructureValue 𝓑 f hf) := by
  intro p
  rcases hf p with ⟨V,hp,i,n,ell,b,hb,hfrac⟩
  have hell : (ell : S) ∈ 𝓑 n := by
    simpa only [add_zero,nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,
      ite_true,Int.toNat_natCast] using ell.property
  refine ⟨V,hp,i,n,⟨(ell : S),hell⟩,b,hb,?_⟩
  intro q
  dsimp only
  apply nativeHomogeneousLocalRingModuleEmbedding_injective 𝓑 q.1
  erw [nativeZeroModuleStructureValue_spec,nativeHomogeneousLocalRingModuleEmbedding_mk]
  exact hfrac q

/-- The native structure-ring section map into the ACTUAL degree-zero
ring-module sections, linear for the same actual structure-ring sections. -/
def nativeStructureRingZeroModuleSectionMap
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U →ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) 0 U where
  toFun r := ⟨fun p => nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (r.1 p),
    nativeStructureLocalFraction_moduleLocalFraction 𝓑 r.property⟩
  map_add' r s := by
    apply Subtype.ext
    funext p
    exact (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1).map_add _ _
  map_smul' r s := by
    apply Subtype.ext
    funext p
    exact (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1).map_smul (r.1 p) (s.1 p)

theorem nativeStructureRingZeroModuleSectionMap_injective
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    Function.Injective (nativeStructureRingZeroModuleSectionMap 𝓑 U) := by
  intro r s hrs
  apply Subtype.ext
  funext p
  apply nativeHomogeneousLocalRingModuleEmbedding_injective 𝓑 p.1
  exact congrArg (fun z => z.1 p) hrs

theorem nativeStructureRingZeroModuleSectionMap_surjective
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    Function.Surjective (nativeStructureRingZeroModuleSectionMap 𝓑 U) := by
  intro f
  refine ⟨⟨nativeZeroModuleStructureValue 𝓑 f.1 f.property,
    nativeZeroModuleStructureValue_localFraction 𝓑 f.1 f.property⟩,?_⟩
  apply Subtype.ext
  funext p
  exact nativeZeroModuleStructureValue_spec 𝓑 f.1 f.property p

/-- Native structure-ring sections are linearly isomorphic to the actual
degree-zero associated ring-module sections on EVERY original open set. -/
def nativeStructureRingZeroModuleSectionEquiv
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U ≃ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) 0 U :=
  LinearEquiv.ofBijective (nativeStructureRingZeroModuleSectionMap 𝓑 U)
    ⟨nativeStructureRingZeroModuleSectionMap_injective 𝓑 U,
      nativeStructureRingZeroModuleSectionMap_surjective 𝓑 U⟩

end LinearStudy
