module
public import Linear.ProjectiveResolutionNativeHomPositiveCohomology
public import Linear.QuotientDerivedModuleExtSupport
public import Linear.AffineKoszulInternalHomComplexIso
public import Linear.TildeComplexExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
variable (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R)
variable (he : ∀ j : ℕ, 0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)

/-- SAME original native Hom cochain computes ACTUAL derived MODULE Ext
in EVERY positive degree,on SAME original CONSTRUCTED Koszul resolution.
SOURCE positive exactness is explicit here and DERIVED for original cuts;
no target coefficient FP/free/flat/invertibility/CM or comparison premise. -/
def affineKoszulNativePositiveCohomologyExtIso (j : ℕ) :
    (affineKoszulNativeHomCochainComplex R N r H).homology (j+1) ≅
      ModuleCat.of R (CategoryTheory.Abelian.Ext.{u}
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (j+1)) :=
  projectiveResolutionNativeHomPositiveCohomologyIso
    (functionKoszulResolutionOfExact H he) N j

/-- The original ACTUAL class morphism agrees with actual original extMk
on native cycles,in every positive degree. The source resolution is retained. -/
theorem affineKoszulNativePositiveCohomologyExtIso_classMap (j : ℕ) :
    (affineKoszulNativeHomCochainComplex R N r H).homologyπ (j+1) ≫
      (affineKoszulNativePositiveCohomologyExtIso R N r H he j).hom =
    ((affineKoszulNativeHomCochainComplex R N r H).cyclesIsoSc' j (j+1) (j+2)
        ((ComplexShape.up ℕ).prev_eq' (by rfl)) ((ComplexShape.up ℕ).next_eq' (by rfl))).hom ≫
      ((affineKoszulNativeHomCochainComplex R N r H).sc' j (j+1) (j+2)).moduleCatCyclesIso.hom ≫
        ModuleCat.ofHom (projectiveResolutionNativeHomCycleExtLinearMap
          (functionKoszulResolutionOfExact H he) N (j+1)) :=
  projectiveResolutionNativeHomPositiveCohomologyIso_classMap
    (functionKoszulResolutionOfExact H he) N j

include he

/-- SAME original ideal I kills EVERY actual native positive Hom cohomology,
using ACTUAL derived module Ext scalar action. N has no added condition. -/
theorem affineKoszulNativePositiveCohomology_ideal_annihilator (j : ℕ) :
    Ideal.span (Set.range H) ≤ Module.annihilator R
      ((affineKoszulNativeHomCochainComplex R N r H).homology (j+1)) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  intro x
  let e := (affineKoszulNativePositiveCohomologyExtIso R N r H he j).toLinearEquiv
  apply e.injective
  rw [map_smul,map_zero]
  exact (Module.mem_annihilator.mp
    ((quotientDerivedModuleExt_ideal_annihilator R (Ideal.span (Set.range H)) N (j+1)) ha)) (e x)

/-- ACTUAL original native positive cohomology is supported in SAME cut,
not in an abstract Ext model. Source exactness comes from original cut proof. -/
theorem affineKoszulNativePositiveCohomology_support_subset (j : ℕ) :
    Module.support R ((affineKoszulNativeHomCochainComplex R N r H).homology (j+1)) ⊆
      PrimeSpectrum.zeroLocus (Ideal.span (Set.range H) : Set R) := by
  intro p hp
  exact (affineKoszulNativePositiveCohomology_ideal_annihilator R N r H he j).trans
    (Module.annihilator_le_of_mem_support hp)

/-- Finite support transfers to ACTUAL original native positive cohomology.
The original finite-cut premise is kept explicit;no coefficient CM condition. -/
theorem affineKoszulNativePositiveCohomology_support_finite (j : ℕ)
    (hI : (PrimeSpectrum.zeroLocus (Ideal.span (Set.range H) : Set R)).Finite) :
    (Module.support R ((affineKoszulNativeHomCochainComplex R N r H).homology (j+1))).Finite :=
  hI.subset (affineKoszulNativePositiveCohomology_support_subset R N r H he j)

attribute [local irreducible] affineKoszulInternalHomCochainComplexIso

/-- Compute ACTUAL internal-Hom SHEAF-COMPLEX positive cohomology as
SAME associated ACTUAL derived MODULE Ext,in every positive degree.
This is NOT a completed derived SHEAF Ext identification or global gluing. -/
def affineKoszulInternalHomPositiveCohomologyExtIso (j : ℕ) :
    (affineKoszulInternalHomCochainComplex R N r H).homology (j+1) ≅
      tilde (ModuleCat.of R (CategoryTheory.Abelian.Ext.{u}
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (j+1))) := by
  letI := tilde_functor_preservesHomology R
  exact HomologicalComplex.homologyMapIso
      (affineKoszulInternalHomCochainComplexIso R N r H).symm (j+1) ≪≫
    ((affineKoszulNativeHomCochainComplex R N r H).sc (j+1)).mapHomologyIso (tilde.functor R) ≪≫
      (tilde.functor R).mapIso (affineKoszulNativePositiveCohomologyExtIso R N r H he j)

end LinearStudy
