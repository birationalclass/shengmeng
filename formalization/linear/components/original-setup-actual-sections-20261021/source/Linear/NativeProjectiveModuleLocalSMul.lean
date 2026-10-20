module
public import Linear.NativeProjectiveModuleLocalAdd
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Module.Pi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S D : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D)
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The native degree-zero local ring acts on the ACTUAL module
localization through its ACTUAL homogeneous-fraction value map. -/
@[instance_reducible] def nativeProjectiveAtPrimeModuleScalar
    (p : ProjectiveSpectrum 𝓑) :
    Module (HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal)
      (nativeProjectiveModuleAtPrime (D := D) 𝓑 p) :=
  Module.compHom _ (algebraMap _ (Localization p.asHomogeneousIdeal.toIdeal.primeCompl))

attribute [local instance] nativeProjectiveAtPrimeModuleScalar

/-- The actual native structure-ring sections act pointwise on the
ambient functions into original module localizations. -/
@[instance_reducible] def nativeProjectiveAmbientSectionModule
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)
      (∀ p : U.unop, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1) :=
  Module.compHom _ (ProjectiveSpectrum.StructureSheaf.sectionsSubring U).subtype

theorem nativeProjectivePrimeFraction_smul (p : ProjectiveSpectrum 𝓑)
    (n : ℕ) (r b : 𝓑 n) (hb : (b : S) ∉ p.asHomogeneousIdeal)
    (ell : D) (c : S) (hc : c ∉ p.asHomogeneousIdeal) :
    (HomogeneousLocalization.mk ⟨n,r,b,hb⟩ :
      HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal) •
        LocalizedModule.mk ell ⟨c,hc⟩ =
      LocalizedModule.mk ((r : S) • ell)
        ⟨(b : S)*c,p.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hb hc⟩ := by
  change (HomogeneousLocalization.mk ⟨n,r,b,hb⟩ :
    HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal).val •
    LocalizedModule.mk ell (⟨c,hc⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl) = _
  rw [HomogeneousLocalization.val_mk]
  exact LocalizedModule.mk_smul_mk _ _ _ _

/-- A native structure-ring fraction times a genuine degree-k module
fraction is again a genuine degree-k fraction on the common open. -/
theorem nativeProjectiveModuleFraction_smul
    (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
    (k : ℤ) {U V : Opens (ProjectiveSpectrum.top 𝓑)}
    {a : ∀ p : U, HomogeneousLocalization.AtPrime 𝓑 p.1.asHomogeneousIdeal.toIdeal}
    {b : ∀ p : V, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1}
    (ha : ProjectiveSpectrum.StructureSheaf.IsFraction a)
    (hb : nativeProjectiveModuleIsFraction 𝓑 𝒟 k b) :
    nativeProjectiveModuleIsFraction 𝓑 𝒟 k
      (fun p : (U ⊓ V : Opens _) => a ⟨p.1,p.2.1⟩ • b ⟨p.1,p.2.2⟩) := by
  rcases ha with ⟨na,ra,sa,hsa,hfa⟩
  rcases hb with ⟨nb,ellb,sb,hsb,hfb⟩
  have hnum : (ra : S) • (ellb : D) ∈ 𝒟 (((na+nb : ℕ) : ℤ)+k) := by
    simpa only [Int.natCast_add,add_assoc]
      using hgrade na ((nb : ℤ)+k) ra ra.property ellb ellb.property
  refine ⟨na+nb,⟨(ra : S) • (ellb : D),hnum⟩,
    ⟨(sa : S)*(sb : S),SetLike.mul_mem_graded sa.property sb.property⟩,?_,?_⟩
  · intro p
    exact p.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hsa ⟨p.1,p.2.1⟩) (hsb ⟨p.1,p.2.2⟩)
  · intro p
    dsimp only
    erw [hfa,hfb]
    exact nativeProjectivePrimeFraction_smul 𝓑 p.1 na ra sa
      (hsa ⟨p.1,p.2.1⟩) (ellb : D) sb (hsb ⟨p.1,p.2.2⟩)

theorem nativeProjectiveModuleLocalPredicate_smul
    (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
    (k : ℤ) {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {a : ∀ p : U, HomogeneousLocalization.AtPrime 𝓑 p.1.asHomogeneousIdeal.toIdeal}
    {b : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1}
    (ha : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝓑).pred a)
    (hb : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred b) :
    (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred (fun p => a p • b p) :=
  PrelocalPredicate.sheafify_inductionOn₂'
    (ProjectiveSpectrum.StructureSheaf.isFractionPrelocal 𝓑)
    (nativeProjectiveModuleFractionPrelocal 𝓑 𝒟 k)
    (nativeProjectiveModuleFractionPrelocal 𝓑 𝒟 k)
    (fun a b => a • b)
    (fun ha hb => nativeProjectiveModuleFraction_smul 𝓑 𝒟 hgrade k ha hb) ha hb

end LinearStudy
