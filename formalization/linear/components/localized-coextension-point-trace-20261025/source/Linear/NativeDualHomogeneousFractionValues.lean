module
public import Linear.NativeDualLocalizationFractionValues
public import Linear.CoextensionGradedModule
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
variable [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Evaluation of two actual degree-zero homogeneous fractions in the
native dual/source belongs to the ACTUAL degree-zero localization of the
normalization base. This constructs the homogeneous value, not a supplied
chart functional or canonical module. -/
theorem finiteNativeDual_degreeZero_fraction_value
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (k d : ℕ)
    (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
    (hell : ell ∈ coextensionGradedPiece 𝒜 𝓑 (k : ℤ))
    (x : S) (hx : x ∈ 𝓑 d) :
    ∃ z : HomogeneousLocalization.Away 𝒜 a,
      z.val = finiteNativeCoextensionLocalizationEquiv
        (Q := Localization.Away a) (Submonoid.powers a) hinj
        (LocalizedModule.mk ell (⟨a^k, ⟨k, rfl⟩⟩ : Submonoid.powers a))
        (LocalizedModule.mk x (⟨a^d, ⟨d, rfl⟩⟩ : Submonoid.powers a)) := by
  have hp := (coextensionGradedPiece_mem_iff 𝒜 𝓑 (k : ℤ) ell).mp hell d x hx
  have hproj : ell x = gradedModuleProjection 𝒜 (d+k) (ell x) := by
    simpa only [← Int.natCast_add, gradedIntegerProjection, Int.natCast_nonneg,
      ite_true, Int.toNat_natCast] using hp
  have hdeg : ell x ∈ 𝒜 (d+k) := by
    rw [hproj]
    exact (DirectSum.decompose 𝒜 (ell x) (d+k)).property
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 ha (d+k) (ell x)
    (by simpa only [smul_eq_mul, mul_one] using hdeg), ?_⟩
  rw [finiteNativeCoextensionLocalizationEquiv_apply_fraction]
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  change IsLocalization.mk' (Localization.Away a) (ell x)
      (⟨a^(d+k), ⟨d+k, rfl⟩⟩ : Submonoid.powers a) =
    IsLocalization.mk' (Localization.Away a) (ell x)
      ((⟨a^k, ⟨k, rfl⟩⟩ : Submonoid.powers a) * ⟨a^d, ⟨d, rfl⟩⟩)
  congr 1
  apply Subtype.ext
  simp only [Submonoid.coe_mul, pow_add, mul_comm]

end LinearStudy
