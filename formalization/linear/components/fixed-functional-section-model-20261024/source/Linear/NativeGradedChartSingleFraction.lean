module
public import Linear.NativeProjectiveChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module K M] [Module R M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- The generated weighted degree-zero module consists of single actual
homogeneous fractions. Closure under chart scalars is proved by their
actual homogeneous fraction representation, with all degrees retained. -/
theorem nativeGradedChart_exists_singleFraction
    (hD : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (x : LocalizedModule (Submonoid.powers a) M)
    (hx : x ∈ nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    ∃ n : ℕ, ∃ m : M, m ∈ 𝒟 ((n*d : ℕ) : ℤ) ∧
      x = LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) := by
  induction hx using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
    exact ⟨0,0,(𝒟 _).zero_mem,by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n,m,hm,rfl⟩ := hx
    obtain ⟨k,l,hl,rfl⟩ := hy
    refine ⟨n+k,a^k • m+a^n • l,?_,?_⟩
    · apply Submodule.add_mem
      · have h := hD (k*d) ((n*d : ℕ) : ℤ) (a^k)
          (by simpa using SetLike.pow_mem_graded k ha) m hm
        simpa only [Nat.add_mul,Int.natCast_add,add_comm] using h
      · have h := hD (n*d) ((k*d : ℕ) : ℤ) (a^n)
          (by simpa using SetLike.pow_mem_graded n ha) l hl
        simpa only [Nat.add_mul,Int.natCast_add] using h
    · rw [LocalizedModule.mk_add_mk]
      congr 1
      apply Subtype.ext
      change a^n*a^k = a^(n+k)
      exact (pow_add a n k).symm
  | smul c x _ hx =>
    obtain ⟨n,m,hm,rfl⟩ := hx
    obtain ⟨k,b,hb,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha c
    refine ⟨k+n,b • m,?_,?_⟩
    · have h := hD (k*d) ((n*d : ℕ) : ℤ) b (by simpa using hb) m hm
      simpa only [Nat.add_mul,Int.natCast_add] using h
    · change (HomogeneousLocalization.Away.mk 𝒜 ha k b hb).val •
        LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) = _
      rw [HomogeneousLocalization.Away.val_mk,LocalizedModule.mk_smul_mk]
      congr 1
      apply Subtype.ext
      change a^k*a^n = a^(k+n)
      exact (pow_add a k n).symm

end LinearStudy
