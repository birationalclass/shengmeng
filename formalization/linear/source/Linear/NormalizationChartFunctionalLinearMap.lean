module
public import Linear.NormalizationChartFunctionalHomogenization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- The actual homogeneous fraction cancels against its denominator in
the ORIGINAL base ring localization. -/
theorem normalizationChartHomogeneousFraction_cancel
    (a : R) (ha : a ∈ 𝒜 1) (k : ℕ) (c : R) (hc : c ∈ 𝒜 k) :
    (algebraMap R (Localization.Away a) a)^k *
      (HomogeneousLocalization.Away.mk 𝒜 ha k c (by simpa using hc)).val =
      algebraMap R (Localization.Away a) c := by
  rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
  simpa only [map_pow] using IsLocalization.mk'_spec' (Localization.Away a) c
    (⟨a^k,⟨k,rfl⟩⟩ : Submonoid.powers a)

/-- The homogenized functional respects the ORIGINAL normalization scalar
action on all homogeneous source and base elements. -/
theorem normalizationChartFunctionalAddMap_smul_homogeneous
    (a : R) (ha : a ∈ 𝒜 1) (haB : algebraMap R S a ∈ 𝓑 1)
    (f : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
      →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a)
    (k n : ℕ) (c : R) (hc : c ∈ 𝒜 k) (b : S) (hb : b ∈ 𝓑 n) :
    normalizationChartFunctionalAddMap 𝒜 𝓑 a haB f (c • b) =
      c • normalizationChartFunctionalAddMap 𝒜 𝓑 a haB f b := by
  rw [normalizationChartFunctionalAddMap_homogeneous 𝒜 𝓑 a haB f
      (k+n) (c • b) (SetLike.GradedSMul.smul_mem hc hb),
    ← normalizationHomogeneousChart_smul_fraction 𝒜 𝓑 a ha haB k n c hc b hb,
    f.map_smul,smul_eq_mul,HomogeneousLocalization.val_mul,
    normalizationChartFunctionalAddMap_homogeneous 𝒜 𝓑 a haB f n b hb,
    Algebra.smul_def,pow_add]
  have h := normalizationChartHomogeneousFraction_cancel 𝒜 a ha k c hc
  calc
    _ = ((algebraMap R (Localization.Away a) a)^k *
        (HomogeneousLocalization.Away.mk 𝒜 ha k c (by simpa using hc)).val) *
        ((algebraMap R (Localization.Away a) a)^n *
          (f (HomogeneousLocalization.Away.mk 𝓑 haB n b (by simpa using hb))).val) := by ring
    _ = _ := by rw [h]

/-- Homogenizing any actual source-chart functional gives an ORIGINAL
R-linear functional on S with localized base values. All scalar elements
are handled by the actual graded decompositions; no free basis is assumed. -/
def normalizationChartFunctionalLinearMap
    (a : R) (ha : a ∈ 𝒜 1) (haB : algebraMap R S a ∈ 𝓑 1)
    (f : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
      →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a) :
    S →ₗ[R] Localization.Away a := {
  normalizationChartFunctionalAddMap 𝒜 𝓑 a haB f with
  map_smul' := by
    intro c b
    change normalizationChartFunctionalAddMap 𝒜 𝓑 a haB f (c • b) =
      c • normalizationChartFunctionalAddMap 𝒜 𝓑 a haB f b
    induction c using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous k c =>
        induction b using DirectSum.Decomposition.inductionOn 𝓑 with
        | zero => simp
        | @homogeneous n b =>
            exact normalizationChartFunctionalAddMap_smul_homogeneous 𝒜 𝓑
              a ha haB f k n c c.property b b.property
        | add b b' hb hb' =>
            rw [smul_add,map_add,hb,hb',map_add,smul_add]
    | add c c' hc hc' => rw [add_smul,map_add,hc,hc',add_smul] }
end LinearStudy
