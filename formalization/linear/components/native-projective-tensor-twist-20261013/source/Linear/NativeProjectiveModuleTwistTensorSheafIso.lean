module
public import Linear.NativeProjectiveModuleTwistTensorLocality
public import Linear.ModuleSheafificationLocalCriterion
public import Linear.ModuleSheafificationAdjunctionMaps
public import Linear.NativeProjectiveModuleTwistTensorSheafMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module S M] [Module K M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : M, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))

variable {ι : Type u} (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
variable (hgen : Algebra.adjoin K (Set.range a) = ⊤)
include ha hgen

/-- For an actual degree-one-generated graded algebra, the genuine
tensor-sheaf multiplication is an isomorphism. Local bijectivity has
been proved on actual native Proj opens, not assumed as a certificate. -/
theorem nativeProjectiveModuleTwistTensorSheafMap_isIso (m : ℕ) (k : ℤ) :
    IsIso (nativeProjectiveModuleTwistTensorSheafMap 𝓑 𝒟 hD m k) := by
  let R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf
  let f := nativeProjectiveModuleTwistTensorPresheafMap 𝓑 𝒟 hD m k
  have hi := nativeProjectiveModuleTwistTensorPresheafMap_locallyInjective
    𝓑 𝒟 hD a ha hgen m k
  have hs := nativeProjectiveModuleTwistTensorPresheafMap_locallySurjective
    𝓑 𝒟 hD a ha hgen m k
  letI : IsIso ((PresheafOfModules.sheafification (𝟙 R.obj)).map f) :=
    (moduleSheafification_isIso_iff_locallyBijective (R := R) (𝟙 R.obj) f).mpr ⟨hi, hs⟩
  unfold nativeProjectiveModuleTwistTensorSheafMap
  exact moduleSheafificationHomEquiv_symm_isIso R
    (P := nativeProjectiveModuleTwistTensorPresheaf 𝓑 𝒟 hD m k)
    (F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD (k+(m : ℤ))) f

/-- Constructed O_Proj-linear isomorphism
T_m(S) tensor T_k(M) ~= T_(k+m)(M) on the actual original native Proj.
The tensor is actual sectionwise tensor followed by module-sheafification.
This does not identify this line-bundle model with the external Serre
pole sheaf, nor prove eventual H1 vanishing. -/
def nativeProjectiveModuleTwistTensorSheafIso (m : ℕ) (k : ℤ) :
    nativeProjectiveModuleTwistTensorSheaf 𝓑 𝒟 hD m k ≅
      nativeProjectiveModuleSheaf 𝓑 𝒟 hD (k+(m : ℤ)) := by
  letI := nativeProjectiveModuleTwistTensorSheafMap_isIso 𝓑 𝒟 hD a ha hgen m k
  exact asIso (nativeProjectiveModuleTwistTensorSheafMap 𝓑 𝒟 hD m k)

end LinearStudy
