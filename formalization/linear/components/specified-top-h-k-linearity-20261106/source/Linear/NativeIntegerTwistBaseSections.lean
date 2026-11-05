module
public import Linear.NativeIntegerTwistFrameTransition
public import Linear.ModuleBaseCechBasic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The actual integer-power frame is linear over global functions of
any actual base of the original Proj scheme. -/
def nativeIntegerTwistBaseSectionEquiv {Y : Scheme.{u}}
    (π : (AlgebraicGeometry.Proj 𝓑) ⟶ Y) (a : S) (ha : a ∈ 𝓑 1) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    (Scheme.Modules.baseModulePresheaf π
      (SheafOfModules.unit (AlgebraicGeometry.Proj 𝓑).ringCatSheaf)).obj U ≃ₗ[
        Γ(Y, (⊤ : Y.Opens))]
      (Scheme.Modules.baseModulePresheaf π
        (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
          (nativeProjectiveRingIntegerPiece_graded 𝓑) k)).obj U :=
  { (nativeIntegerTwistSectionFrame 𝓑 a ha k U hp).toAddEquiv with
    map_smul' := by
      intro r s
      let c : (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U :=
        ((AlgebraicGeometry.Proj 𝓑).presheaf.map
          (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom (π.appTop.hom r)
      change nativeIntegerTwistSectionFrame 𝓑 a ha k U hp
        (c * (show (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U from s)) =
        c • nativeIntegerTwistSectionFrame 𝓑 a ha k U hp s
      exact (nativeIntegerTwistSectionFrame 𝓑 a ha k U hp).map_smul c
        (show (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U from s) }

/-- The actual base-linear frame commutes with every original open
restriction within the same nonvanishing coordinate chart. -/
theorem nativeIntegerTwistBaseSectionEquiv_restrict {Y : Scheme.{u}}
    (π : (AlgebraicGeometry.Proj 𝓑) ⟶ Y) (a : S) (ha : a ∈ 𝓑 1) (k : ℤ)
    {U V : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ} (i : U ⟶ V)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (r : (Scheme.Modules.baseModulePresheaf π
      (SheafOfModules.unit (AlgebraicGeometry.Proj 𝓑).ringCatSheaf)).obj U) :
    (Scheme.Modules.baseModulePresheaf π
      (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k)).map i
        (nativeIntegerTwistBaseSectionEquiv 𝓑 π a ha k U hp r) =
      nativeIntegerTwistBaseSectionEquiv 𝓑 π a ha k V (fun p => hp (i.unop p))
        ((Scheme.Modules.baseModulePresheaf π
          (SheafOfModules.unit (AlgebraicGeometry.Proj 𝓑).ringCatSheaf)).map i r) :=
  nativeIntegerTwistSectionFrame_restrict 𝓑 a ha k i hp r

end LinearStudy
