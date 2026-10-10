module
public import Linear.NormalizationHomogeneousCoefficientProjection
public import Linear.NormalizationChartFunctionalLinearMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
universe u
variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]

/-- An original integral element whose localized value is degree n is
already in the original degree-n piece. Injectivity of the ACTUAL
localization, not a domain/free-module replacement, justifies cancellation. -/
theorem homogeneousLocalization_integral_value_mem
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (n : ℕ) (x : R) (w : HomogeneousLocalization.Away 𝒜 a)
    (h : algebraMap R (Localization.Away a) x =
      (algebraMap R (Localization.Away a) a)^n * w.val) : x ∈ 𝒜 n := by
  obtain ⟨e,c,hc,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha w
  have hc' : c ∈ 𝒜 e := by simpa using hc
  have he : a^e ∈ 𝒜 e := by
    simpa using SetLike.pow_mem_graded e ha
  have hn : a^n ∈ 𝒜 n := by
    simpa using SetLike.pow_mem_graded n ha
  have hi : x * a^e = c * a^n := by
    apply hinj
    rw [map_mul,map_mul,map_pow,map_pow,h]
    rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
    have hs := IsLocalization.mk'_spec (Localization.Away a) c
      (⟨a^e,⟨e,rfl⟩⟩ : Submonoid.powers a)
    simp only [map_pow] at hs
    calc
      _ = (algebraMap R (Localization.Away a) a)^n *
        (IsLocalization.mk' (Localization.Away a) c
          (⟨a^e,⟨e,rfl⟩⟩ : Submonoid.powers a) *
          (algebraMap R (Localization.Away a) a)^e) := by ring
      _ = _ := by rw [hs]; ring
  have hp := congrArg (gradedModuleProjection 𝒜 (n+e)) hi
  have hcprod : c * a^n ∈ 𝒜 (e+n) := SetLike.mul_mem_graded hc' hn
  have hleft := normalizationProjection_smul_source_homogeneous 𝒜 𝒜
    e (n+e) x (a^e) he
  simp only [smul_eq_mul,Nat.le_add_left,ite_true,Nat.add_sub_cancel] at hleft
  rw [hleft,gradedModuleProjection_on_piece 𝒜 (n+e) (e+n) (c*a^n) hcprod] at hp
  simp only [Nat.add_comm,ite_true] at hp
  have hx : x = gradedModuleProjection 𝒜 n x := by
    apply hinj
    apply (IsLocalization.map_units (Localization.Away a)
      (⟨a^e,⟨e,rfl⟩⟩ : Submonoid.powers a)).mul_left_inj.mp
    change algebraMap R (Localization.Away a) x *
        algebraMap R (Localization.Away a) (a^e) =
      algebraMap R (Localization.Away a) (gradedModuleProjection 𝒜 n x) *
        algebraMap R (Localization.Away a) (a^e)
    rw [← map_mul,← map_mul,hi,hp]
  rw [hx]
  exact (DirectSum.decompose 𝒜 x n).property
end LinearStudy
