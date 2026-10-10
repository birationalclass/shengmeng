module
public import Linear.NativeGradedModuleOverlapMap
public import Linear.NormalizationSourceChartEquiv
public import Linear.NativeProjectiveRingIntegerPieces
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The actual source ring integer grading respects the original
normalization base action. -/
theorem normalizationSourceBaseGradeCompatibility :
    ∀ n : ℕ, ∀ d : ℤ, ∀ a : R, a ∈ 𝒜 n →
      ∀ x : S, x ∈ nativeProjectiveRingIntegerPiece 𝓑 d →
        a • x ∈ nativeProjectiveRingIntegerPiece 𝓑 ((n : ℤ)+d) := by
  intro n d a ha x hx
  rw [Algebra.smul_def]
  exact nativeProjectiveRingIntegerPiece_graded 𝓑 n d (algebraMap R S a)
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) x hx

/-- The original generated source chart is exactly its actual integer
degree-zero module. This retains the original source localization. -/
theorem nativeNormalizationSourceAwayZero_eqIntegerZero (a : R) :
    nativeNormalizationSourceAwayZero 𝒜 𝓑 a =
      nativeGradedModuleAwayZero 𝒜 (nativeProjectiveRingIntegerPiece 𝓑) a := by
  simp only [nativeNormalizationSourceAwayZero,nativeGradedModuleAwayZero,
    nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,ite_true,Int.toNat_natCast]

/-- Construct the actual source degree-zero restriction into the correct
degree-two overlap module, over the actual homogeneous base ring map. -/
def nativeNormalizationSourceOverlapMap
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) :
    nativeNormalizationSourceAwayZero 𝒜 𝓑 a
      →ₛₗ[HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)]
        nativeGradedModuleAwayDegreeZero 𝒜 (nativeProjectiveRingIntegerPiece 𝓑) 2 (a*b) where
  toFun x := ⟨originalLocalizedModuleAwayOverlap a b x.val,
    nativeGradedModuleAwayZero_overlap_mem 𝒜 (nativeProjectiveRingIntegerPiece 𝓑)
      (normalizationSourceBaseGradeCompatibility 𝒜 𝓑) a b ha hb x.val
      ((nativeNormalizationSourceAwayZero_eqIntegerZero 𝒜 𝓑 a) ▸ x.property)⟩
  map_add' x y := Subtype.ext ((originalLocalizedModuleAwayOverlap a b).map_add x.val y.val)
  map_smul' c x := Subtype.ext (originalHomogeneousModuleOverlap_smul 𝒜 a b ha hb c x.val)
end LinearStudy
