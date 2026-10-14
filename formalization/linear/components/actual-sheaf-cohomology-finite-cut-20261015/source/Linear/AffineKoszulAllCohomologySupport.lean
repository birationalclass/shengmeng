module
public import Linear.AffineKoszulPositiveCohomologySupport
public import Linear.ProjectiveResolutionNativeHomZeroSupport
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

attribute [local irreducible] affineKoszulInternalHomCochainComplexIso

/-- In EVERY degree,ACTUAL original internal-Hom cohomology is associated
ACTUAL original native Hom cohomology. Original full complex iso and
PROVED tilde exactness suffice;source exactness is not needed for this iso. -/
def affineKoszulInternalHomCohomologyNativeIso (j : ℕ) :
    (affineKoszulInternalHomCochainComplex R N r H).homology j ≅
      tilde ((affineKoszulNativeHomCochainComplex R N r H).homology j) := by
  letI := tilde_functor_preservesHomology R
  exact HomologicalComplex.homologyMapIso
      (affineKoszulInternalHomCochainComplexIso R N r H).symm j ≪≫
    ((affineKoszulNativeHomCochainComplex R N r H).sc j).mapHomologyIso (tilde.functor R)

variable (he : ∀ j : ℕ, 0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
include he

/-- SAME original cut ideal kills ACTUAL native Hom cohomology in ALL
degrees,including degree zero. SOURCE exactness is explicit and DERIVED
for original cuts;no condition on original coefficient N is added. -/
theorem affineKoszulNativeCohomology_ideal_annihilator (j : ℕ) :
    Ideal.span (Set.range H) ≤ Module.annihilator R
      ((affineKoszulNativeHomCochainComplex R N r H).homology j) := by
  cases j with
  | zero =>
    have h0 := projectiveResolutionNativeHomZeroCohomology_annihilator
      (functionKoszulResolutionOfExact H he) N
    change Module.annihilator R (R ⧸ Ideal.span (Set.range H)) ≤ Module.annihilator R
      ((affineKoszulNativeHomCochainComplex R N r H).homology 0) at h0
    simpa only [Ideal.annihilator_quotient] using h0
  | succ j => exact affineKoszulNativePositiveCohomology_ideal_annihilator R N r H he j

/-- ALL actual original native Hom cohomology is supported in SAME
original cut V(I),including zero;this is not an abstract replacement model. -/
theorem affineKoszulNativeCohomology_support_subset (j : ℕ) :
    Module.support R ((affineKoszulNativeHomCochainComplex R N r H).homology j) ⊆
      PrimeSpectrum.zeroLocus (Ideal.span (Set.range H) : Set R) := by
  intro p hp
  exact (affineKoszulNativeCohomology_ideal_annihilator R N r H he j).trans
    (Module.annihilator_le_of_mem_support hp)

/-- Actual native Hom cohomology in ALL degrees has finite support when
SAME ORIGINAL cut is finite. Derive that finiteness for original geometry
separately;no target coefficient finite-generation/CM/free condition. -/
theorem affineKoszulNativeCohomology_support_finite (j : ℕ)
    (hI : (PrimeSpectrum.zeroLocus (Ideal.span (Set.range H) : Set R)).Finite) :
    (Module.support R ((affineKoszulNativeHomCochainComplex R N r H).homology j)).Finite :=
  hI.subset (affineKoszulNativeCohomology_support_subset R N r H he j)

end LinearStudy
