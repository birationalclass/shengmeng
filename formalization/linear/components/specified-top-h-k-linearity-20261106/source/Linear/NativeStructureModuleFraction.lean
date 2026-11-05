module
public import Linear.NativeProjectiveRingModuleLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Native structure-ring homogeneous fractions become precisely actual
degree-zero ring-module fractions under the canonical local embedding. -/
theorem nativeStructureFraction_moduleFraction
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {f : ∀ p : U, HomogeneousLocalization.AtPrime 𝓑 p.1.asHomogeneousIdeal.toIdeal}
    (hf : ProjectiveSpectrum.StructureSheaf.IsFraction f) :
    nativeProjectiveModuleIsFraction 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) 0
      (fun p => nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (f p)) := by
  rcases hf with ⟨n,a,b,hb,hf⟩
  have ha : (a : S) ∈ nativeProjectiveRingIntegerPiece 𝓑 ((n : ℤ)+0) := by
    simpa only [add_zero,nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,
      ite_true,Int.toNat_natCast] using a.property
  refine ⟨n,⟨(a : S),ha⟩,b,hb,?_⟩
  intro p
  dsimp only
  erw [hf]
  exact nativeHomogeneousLocalRingModuleEmbedding_mk 𝓑 p.1 n a b (hb p)

theorem nativeStructureLocalFraction_moduleLocalFraction
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {f : ∀ p : U, HomogeneousLocalization.AtPrime 𝓑 p.1.asHomogeneousIdeal.toIdeal}
    (hf : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝓑).pred f) :
    (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) 0).pred
      (fun p => nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (f p)) := by
  intro p
  rcases hf p with ⟨V,hp,i,hf⟩
  exact ⟨V,hp,i,nativeStructureFraction_moduleFraction 𝓑 hf⟩

/-- Every value of an ACTUAL degree-zero module section lies in the
canonical image of the actual native homogeneous local ring. -/
theorem nativeZeroModuleLocalFraction_value_in_structure_image
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1}
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑) 0).pred f) (p : U) :
    ∃ z : HomogeneousLocalization.AtPrime 𝓑 p.1.asHomogeneousIdeal.toIdeal,
      nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 z = f p := by
  rcases hf p with ⟨V,hp,i,n,ell,b,hb,hf⟩
  have hell : (ell : S) ∈ 𝓑 n := by
    simpa only [add_zero,nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,
      ite_true,Int.toNat_natCast] using ell.property
  let q : V := ⟨p.1,hp⟩
  refine ⟨HomogeneousLocalization.mk ⟨n,⟨(ell : S),hell⟩,b,hb q⟩,?_⟩
  rw [nativeHomogeneousLocalRingModuleEmbedding_mk]
  have h := hf q
  change f p = LocalizedModule.mk (ell : S) ⟨(b : S),hb q⟩ at h
  exact h.symm

end LinearStudy
