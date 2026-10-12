module
public import Linear.NativeProjectiveFiniteGradedFinitePresentation
public import Linear.NativeProjectiveKernelSheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {K S E F : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup E] [Module K E] [Module S E] [IsScalarTower K S E]
variable [AddCommGroup F] [Module K F] [Module S F]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (ℰ : ℤ → Submodule K E) (ℱ : ℤ → Submodule K F)
variable [DirectSum.Decomposition ℰ] [DirectSum.Decomposition ℱ]
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → c • x ∈ ℰ ((n : ℤ) + d))
variable (hF : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : F, x ∈ ℱ d → c • x ∈ ℱ ((n : ℤ) + d))
variable (b : E →ₗ[S] F)
variable (hh : ∀ d : ℤ, ∀ x : E, x ∈ ℰ d → b x ∈ ℱ d)

/-- Let the actual graded source module E be finite over a Noetherian S,
and let actual degree-one basic opens cover Proj. Then the ACTUAL
categorical kernel of its untwisted native associated-sheaf map is finitely
presented. Algebraic kernel finiteness, its graded decomposition and the
native-to-categorical-kernel comparison are DERIVED from b; no kernel
finiteness or comparison certificate is assumed. This supplies the next
Serre-presentation step. Positive twists, actual I_V comparison, eventual
H1 vanishing and original4.1/4.2 completion remain separate obligations. -/
theorem nativeProjectiveKernel_isFinitePresentation_of_cover
    [IsNoetherianRing S] [Module.Finite S E] {ι : Type u}
    (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (kernel (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh 0)).IsFinitePresentation := by
  let 𝒦 := nativeProjectiveKernelPiece ℰ b
  let hK := nativeProjectiveKernelPiece_graded 𝓑 ℰ b hE
  letI : DirectSum.Decomposition 𝒦 := nativeProjectiveKernelDecomposition ℰ ℱ b hh
  letI : IsNoetherian S E := isNoetherian_of_isNoetherianRing_of_finite S E
  letI : IsNoetherian S b.ker := isNoetherian_of_submodule_of_noetherian S E b.ker (inferInstance : IsNoetherian S E)
  letI : Module.Finite S b.ker := inferInstance
  letI : (nativeProjectiveModuleSheaf 𝓑 𝒦 hK 0).IsFinitePresentation :=
    nativeFiniteGraded_isFinitePresentation_of_cover 𝓑 𝒦 hK a ha hcover
  let eIso : nativeProjectiveModuleSheaf 𝓑 𝒦 hK 0 ≅
      kernel (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh 0) :=
    (nativeProjectiveKernelSheafIsLimit 𝓑 ℰ ℱ hE hF b hh 0).conePointUniqueUpToIso
      (limit.isLimit (parallelPair (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh 0) 0))
  exact (SheafOfModules.isFinitePresentation (AlgebraicGeometry.Proj 𝓑).ringCatSheaf).prop_of_iso
    eIso inferInstance
end LinearStudy
