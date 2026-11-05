module
public import Linear.NativeProjectiveKernelSheaf
public import Linear.NativeProjectiveDegreeZeroEpi
public import Linear.NativeProjectiveDegreeZeroComposition
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Limits
universe u
variable {K S D E F : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module K D] [Module S D]
variable [AddCommGroup E] [Module K E] [Module S E] [IsScalarTower K S E]
variable [AddCommGroup F] [Module K F] [Module S F]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E) (ℱ : ℤ → Submodule K F)
variable [DirectSum.Decomposition 𝒟] [DirectSum.Decomposition ℰ]
variable [DirectSum.Decomposition ℱ]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : D, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n : ℤ) + d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → c • x ∈ ℰ ((n : ℤ) + d))
variable (hF : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : F, x ∈ ℱ d → c • x ∈ ℱ ((n : ℤ) + d))
variable (a : D →ₗ[S] E) (b : E →ₗ[S] F)
variable (ha : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → a x ∈ ℰ d)
variable (hb : ∀ d : ℤ, ∀ x : E, x ∈ ℰ d → b x ∈ ℱ d)

/-- Actual module exactness gives a genuine zero composite of native
associated-sheaf maps, over the original projective scheme. -/
theorem nativeProjectiveDegreeZeroSheafMap_comp_zero
    (hex : LinearMap.range a = b.ker) (k : ℤ) :
    nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE a ha k ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hb k = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  exact (nativeProjectiveModuleAtPrimeMap_exact 𝓑 a b
    (LinearMap.exact_iff.mpr hex.symm) p.1).apply_apply_eq_zero (x.1 p)

/-- Exactness of ACTUAL native associated sheaves, derived from ordinary
homogeneous module exactness. The relation map factors epimorphically
through the actual graded kernel; its native sheaf is proved to be the
categorical kernel, rather than assumed as a model. -/
theorem nativeProjectiveDegreeZeroSheafMap_exact
    (hex : LinearMap.range a = b.ker) (k : ℤ) :
    (ShortComplex.mk
      (nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE a ha k)
      (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hb k)
      (nativeProjectiveDegreeZeroSheafMap_comp_zero 𝓑 𝒟 ℰ ℱ
        hD hE hF a b ha hb hex k)).Exact := by
  let 𝒦 := nativeProjectiveKernelPiece ℰ b
  let hK := nativeProjectiveKernelPiece_graded 𝓑 ℰ b hE
  letI := nativeProjectiveKernelDecomposition ℰ ℱ b hb
  have hm : ∀ x : D, a x ∈ b.ker := fun x => hex ▸ ⟨x, rfl⟩
  let a0 : D →ₗ[S] b.ker := a.codRestrict b.ker hm
  have ha0 : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → a0 x ∈ 𝒦 d :=
    fun d x hx => ha d x hx
  have hs : Function.Surjective a0 := by
    intro x
    have hx : (x : E) ∈ LinearMap.range a := hex.symm ▸ x.property
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  let α := nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE a ha k
  let β := nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hb k
  let γ := nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 𝒦 hD hK a0 ha0 k
  let δ := nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k
  letI : Epi γ := nativeProjectiveDegreeZeroSheafMap_epi
    𝓑 𝒟 𝒦 hD hK a0 ha0 hs k
  have hfac : γ ≫ δ = α := by
    change nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 𝒦 hD hK a0 ha0 k ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 𝒦 ℰ hK hE b.ker.subtype
        (fun _ _ hx => hx) k = _
    rw [nativeProjectiveDegreeZeroSheafMap_comp]
    rfl
  let w := nativeProjectiveDegreeZeroSheafMap_comp_zero 𝓑 𝒟 ℰ ℱ
    hD hE hF a b ha hb hex k
  let wK := nativeProjectiveKernelSheafInclusion_comp_zero 𝓑 ℰ ℱ hE hF b hb k
  let C := ShortComplex.mk α β w
  let C' := ShortComplex.mk δ β wK
  let φ : C ⟶ C' :=
    { τ₁ := γ
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simpa only [Category.comp_id] using hfac
      comm₂₃ := by
        change (𝟙 _) ≫ β = β ≫ 𝟙 _
        simp }
  have hCK : C'.Exact := C'.exact_of_f_is_kernel
    (nativeProjectiveKernelSheafIsLimit 𝓑 ℰ ℱ hE hF b hb k)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hCK

end LinearStudy
