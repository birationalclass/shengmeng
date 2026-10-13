module
public import Linear.NativeProjectiveOrderedCechExact
public import Linear.NativeProjectiveKernelTwistFinitePresentation
public import Linear.NativeProjectiveDegreeZeroEpi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K S E F : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup E] [Module K E] [Module S E] [IsScalarTower K S E]
variable [AddCommGroup F] [Module K F] [Module S F] [IsScalarTower K S F]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (ℰ : ℤ → Submodule K E) (ℱ : ℤ → Submodule K F)
variable [DirectSum.Decomposition ℰ] [DirectSum.Decomposition ℱ]
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → c • x ∈ ℰ ((n : ℤ)+d))
variable (hF : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : F, x ∈ ℱ d → c • x ∈ ℱ ((n : ℤ)+d))
variable (b : E →ₗ[S] F) (hh : ∀ d : ℤ, ∀ x : E, x ∈ ℰ d → b x ∈ ℱ d)
variable {ι : Type u} [LinearOrder ι]
variable (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
variable (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤)
variable {Y : Scheme.{u}} (π : AlgebraicGeometry.Proj 𝓑 ⟶ Y)

omit [IsScalarTower K S F] in
/-- The actual native sheaves of a homogeneous surjection and its actual
module kernel form a short exact sequence, for every integer twist. -/
theorem nativeProjectiveGradedKernelSheaves_shortExact
    (hb : Function.Surjective b) (k : ℤ) :
    (ShortComplex.mk
      (nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k)
      (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh k)
      (nativeProjectiveKernelSheafInclusion_comp_zero 𝓑 ℰ ℱ hE hF b hh k)).ShortExact := by
  let T := ShortComplex.mk
    (nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k)
    (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh k)
    (nativeProjectiveKernelSheafInclusion_comp_zero 𝓑 ℰ ℱ hE hF b hh k)
  have hlim := nativeProjectiveKernelSheafIsLimit 𝓑 ℰ ℱ hE hF b hh k
  haveI : Mono T.f := Fork.IsLimit.mono hlim
  haveI : Epi T.g := nativeProjectiveDegreeZeroSheafMap_epi 𝓑 ℰ ℱ hE hF b hh hb k
  exact { exact := T.exact_of_f_is_kernel hlim }

include ha hcover in
/-- A finite homogeneous surjection over a Noetherian graded ring gives
a short exact sequence of actual native ordered Cech complexes at every
integer twist. Quasicoherence of all three sheaves, including the actual
kernel, is derived from the previously checked finite presentations. -/
theorem nativeProjectiveGradedKernelOrderedCech_shortExact
    [IsNoetherianRing S] [Module.Finite S E]
    (hb : Function.Surjective b) (k : ℤ) :
    ((ShortComplex.mk
      (nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k)
      (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh k)
      (nativeProjectiveKernelSheafInclusion_comp_zero 𝓑 ℰ ℱ hE hF b hh k)).map
      (Scheme.Modules.orderedBaseCechComplexFunctor π
        (fun i => Proj.basicOpen 𝓑 (a i)))).ShortExact := by
  let 𝒦 := nativeProjectiveKernelPiece ℰ b
  let hK := nativeProjectiveKernelPiece_graded 𝓑 ℰ b hE
  letI : DirectSum.Decomposition 𝒦 := nativeProjectiveKernelDecomposition ℰ ℱ b hh
  letI : IsNoetherian S E := isNoetherian_of_isNoetherianRing_of_finite S E
  letI : IsNoetherian S b.ker := isNoetherian_of_submodule_of_noetherian S E b.ker inferInstance
  letI : Module.Finite S b.ker := inferInstance
  letI : Module.Finite S F := Module.Finite.of_surjective b hb
  letI : (nativeProjectiveModuleSheaf 𝓑 𝒦 hK k).IsFinitePresentation :=
    nativeFiniteGradedTwist_isFinitePresentation_of_cover 𝓑 𝒦 hK k a ha hcover
  letI : (nativeProjectiveModuleSheaf 𝓑 ℰ hE k).IsFinitePresentation :=
    nativeFiniteGradedTwist_isFinitePresentation_of_cover 𝓑 ℰ hE k a ha hcover
  letI : (nativeProjectiveModuleSheaf 𝓑 ℱ hF k).IsFinitePresentation :=
    nativeFiniteGradedTwist_isFinitePresentation_of_cover 𝓑 ℱ hF k a ha hcover
  let T := ShortComplex.mk
    (nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k)
    (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh k)
    (nativeProjectiveKernelSheafInclusion_comp_zero 𝓑 ℰ ℱ hE hF b hh k)
  letI : T.X₁.IsQuasicoherent := by
    change (nativeProjectiveModuleSheaf 𝓑 𝒦 hK k).IsQuasicoherent
    infer_instance
  letI : T.X₂.IsQuasicoherent := by
    change (nativeProjectiveModuleSheaf 𝓑 ℰ hE k).IsQuasicoherent
    infer_instance
  letI : T.X₃.IsQuasicoherent := by
    change (nativeProjectiveModuleSheaf 𝓑 ℱ hF k).IsQuasicoherent
    infer_instance
  change (T.map _).ShortExact
  exact nativeProjectiveOrderedCech_shortExact 𝓑 a ha π
    (nativeProjectiveGradedKernelSheaves_shortExact 𝓑 ℰ ℱ hE hF b hh hb k)

end LinearStudy
