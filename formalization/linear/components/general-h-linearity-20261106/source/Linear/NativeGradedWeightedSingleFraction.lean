module
public import Linear.NativeGradedWeightedOverlap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
/-- Every element of the ACTUAL span-defined weighted zero chart is one
homogeneous fraction. The proof adapts the common-denominator arithmetic
in ProjConstruction/Proj (ed778ef...), Grading/LocalizedModule.lean, to the
ORIGINAL native span and pinned mathlib objects; no decomposition certificate
or alternative localization object is supplied. -/
theorem nativeGradedModuleAwayDegreeZero_exists_fraction
    (hgrade : ∀ n : ℕ, ∀ j : ℤ, ∀ c : R, c ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → c • m ∈ 𝒟 ((n : ℤ)+j))
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (x : LocalizedModule (Submonoid.powers a) M)
    (hx : x ∈ nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    ∃ n : ℕ, ∃ m : M, m ∈ 𝒟 ((n*d : ℕ):ℤ) ∧
      x = LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) := by
  induction hx using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
    refine ⟨0,0,Submodule.zero_mem _,?_⟩
    simp only [LocalizedModule.zero_mk]
  | add x y _ _ hx hy =>
    obtain ⟨n,m,hm,rfl⟩ := hx
    obtain ⟨k,l,hl,rfl⟩ := hy
    refine ⟨n+k,a^k • m + a^n • l,?_,?_⟩
    · apply Submodule.add_mem
      · have h := hgrade (k*d) ((n*d:ℕ):ℤ) (a^k)
          (by simpa only [smul_eq_mul] using SetLike.pow_mem_graded k ha) m hm
        simpa only [add_mul,Int.natCast_add,add_comm] using h
      · have h := hgrade (n*d) ((k*d:ℕ):ℤ) (a^n)
          (by simpa only [smul_eq_mul] using SetLike.pow_mem_graded n ha) l hl
        simpa only [add_mul,Int.natCast_add,add_comm] using h
    · rw [LocalizedModule.mk_add_mk]
      congr 1
      apply Subtype.ext
      exact (pow_add a n k).symm
  | smul c x _ hx =>
    obtain ⟨n,m,hm,rfl⟩ := hx
    obtain ⟨k,z,hz,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha c
    refine ⟨k+n,z • m,?_,?_⟩
    · have h := hgrade (k*d) ((n*d:ℕ):ℤ) z
        (by simpa only [smul_eq_mul] using hz) m hm
      simpa only [add_mul,Int.natCast_add,add_comm] using h
    · change (HomogeneousLocalization.Away.mk 𝒜 ha k z hz).val •
        LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) =
        LocalizedModule.mk (z • m) (⟨a^(k+n),⟨k+n,rfl⟩⟩ : Submonoid.powers a)
      rw [HomogeneousLocalization.Away.val_mk,LocalizedModule.mk_smul_mk]
      congr 1
      apply Subtype.ext
      exact (pow_add a k n).symm
end LinearStudy
