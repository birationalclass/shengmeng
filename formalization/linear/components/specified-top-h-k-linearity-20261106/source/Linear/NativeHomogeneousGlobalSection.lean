module
public import Linear.NativeProjectiveRingIntegerPieces
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {K S D : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D)
variable (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))

/-- An actual homogeneous element yields an actual global section on the
native Proj: at every homogeneous prime the fraction is ell/1.
No global-section surjectivity or Serre-extension assertion is assumed. -/
def nativeProjectiveModuleHomogeneousGlobalSection (k : ℤ) (ell : 𝒟 k) :
    Γ(nativeProjectiveModuleSheaf 𝓑 𝒟 hgrade k, ⊤) := by
  change nativeProjectiveModuleSections 𝓑 𝒟 hgrade k (op ⊤)
  refine ⟨fun p => LocalizedModule.mk (ell : D) 1,?_⟩
  intro p
  refine ⟨⊤,p.property,𝟙 _,0,⟨(ell : D),?_⟩,
    ⟨1,SetLike.one_mem_graded 𝓑⟩,?_,?_⟩
  · simpa only [Nat.cast_zero,zero_add] using ell.property
  · intro q
    letI : (q.1 : ProjectiveSpectrum 𝓑).asHomogeneousIdeal.toIdeal.IsPrime :=
      (q.1 : ProjectiveSpectrum 𝓑).isPrime
    exact q.1.asHomogeneousIdeal.toIdeal.one_notMem
  · intro q
    rfl

/-- The constructed global section has the ORIGINAL localized value
ell/1, rather than an independently supplied section comparison. -/
theorem nativeProjectiveModuleHomogeneousGlobalSection_apply
    (k : ℤ) (ell : 𝒟 k) (p : (⊤ : (Proj 𝓑).Opens)) :
    (nativeProjectiveModuleHomogeneousGlobalSection 𝓑 𝒟 hgrade k ell).1 p =
      LocalizedModule.mk (ell : D) 1 := rfl

/-- Zero homogeneous element gives zero global section. The converse
will require the appropriate localization-injectivity hypotheses. -/
theorem nativeProjectiveModuleHomogeneousGlobalSection_zero (k : ℤ) :
    nativeProjectiveModuleHomogeneousGlobalSection 𝓑 𝒟 hgrade k 0 = 0 := by
  apply Subtype.ext
  funext p
  exact LocalizedModule.zero_mk _

/-- A nonzero polynomial section cannot come from the zero homogeneous
class. This implication needs no nonempty-Proj or domain assumption. -/
theorem nativeProjectiveModuleHomogeneousGlobalSection_element_ne_zero
    (k : ℤ) (ell : 𝒟 k)
    (hs : nativeProjectiveModuleHomogeneousGlobalSection 𝓑 𝒟 hgrade k ell ≠ 0) :
    (ell : D) ≠ 0 := by
  intro hz
  have hell : ell = (0 : 𝒟 k) := Subtype.ext hz
  apply hs
  rw [hell]
  exact nativeProjectiveModuleHomogeneousGlobalSection_zero 𝓑 𝒟 hgrade k

/-- For a torsion-free module, one ACTUAL homogeneous prime detects
zero of the homogeneous element. The point is explicit: no unproved
nonempty-Proj assertion is hidden in the type. -/
theorem nativeProjectiveModuleHomogeneousGlobalSection_eq_zero_iff_of_point
    [NoZeroSMulDivisors S D] (k : ℤ) (ell : 𝒟 k) (p : ProjectiveSpectrum 𝓑) :
    nativeProjectiveModuleHomogeneousGlobalSection 𝓑 𝒟 hgrade k ell = 0 ↔
      (ell : D) = 0 := by
  constructor
  · intro hs
    have hp : LocalizedModule.mk (ell : D) (1 : p.asHomogeneousIdeal.toIdeal.primeCompl) = 0 :=
      congrArg (fun t => t.1 ⟨p,by trivial⟩) hs
    change (LocalizedModule.mkLinearMap p.asHomogeneousIdeal.toIdeal.primeCompl D)
      (ell : D) = 0 at hp
    obtain ⟨t,ht⟩ := (IsLocalizedModule.eq_zero_iff
      p.asHomogeneousIdeal.toIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asHomogeneousIdeal.toIdeal.primeCompl D)).mp hp
    change (t : S) • (ell : D) = 0 at ht
    have ht0 : (t : S) ≠ 0 := by
      intro hz
      have hnot : (t : S) ∉ p.asHomogeneousIdeal.toIdeal := t.property
      apply hnot
      rw [hz]
      exact p.asHomogeneousIdeal.toIdeal.zero_mem
    exact (eq_zero_or_eq_zero_of_smul_eq_zero ht).resolve_left ht0
  · intro hz
    rw [show ell = (0 : 𝒟 k) from Subtype.ext hz]
    exact nativeProjectiveModuleHomogeneousGlobalSection_zero 𝓑 𝒟 hgrade k
end LinearStudy
