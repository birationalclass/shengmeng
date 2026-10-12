module
public import Linear.NormalizationSourceChartSpan
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
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- A finite ORIGINAL graded normalization makes its FULL actual source
chart finite over its actual base chart. Homogeneous generators and their
degree bound are constructed here from Module.Finite R S. Neither finite
chart generation nor a graded/free basis is an additional hypothesis. -/
theorem normalizationHomogeneousChart_finite [Module.Finite R S]
    (a : R) (ha : a ∈ 𝒜 1) :
    Module.Finite (HomogeneousLocalization.Away 𝒜 a)
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) := by
  classical
  have haB : algebraMap R S a ∈ 𝓑 1 := by
    simpa only [Algebra.smul_def,mul_one,vadd_eq_add,add_zero] using
      SetLike.GradedSMul.smul_mem ha (SetLike.one_mem_graded 𝓑)
  obtain ⟨s,hs,hpieces⟩ := finiteModule_exists_homogeneous_generators (A := R) 𝓑
  let degree : s → ℕ := fun i => (hpieces i.val i.property).choose
  let gen : s → S := Subtype.val
  have hgen (i : s) : gen i ∈ 𝓑 (degree i) :=
    (hpieces i.val i.property).choose_spec
  have hrange : Set.range gen = (s : Set S) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact i.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  have hspan : Submodule.span R (Set.range gen) = ⊤ := by rwa [hrange]
  let m := Finset.univ.sup degree
  have hbound (i : s) : degree i ≤ m := Finset.le_sup (Finset.mem_univ i)
  let chartGen : s → HomogeneousLocalization.Away 𝓑 (algebraMap R S a) :=
    fun i => HomogeneousLocalization.Away.mk 𝓑 haB (degree i) (gen i)
      (by simpa using hgen i)
  have hchart : Submodule.span (HomogeneousLocalization.Away 𝒜 a)
      (Set.range chartGen) = ⊤ :=
    normalizationHomogeneousChart_span 𝒜 𝓑 a ha haB degree gen hgen hspan m hbound
  let M := Submodule.span (HomogeneousLocalization.Away 𝒜 a) (Set.range chartGen)
  letI : Module.Finite (HomogeneousLocalization.Away 𝒜 a) M :=
    Module.Finite.span_of_finite _ (Set.finite_range chartGen)
  apply Module.Finite.of_surjective (Submodule.subtype M)
  intro z
  refine ⟨⟨z,?_⟩,rfl⟩
  change z ∈ Submodule.span (HomogeneousLocalization.Away 𝒜 a) (Set.range chartGen)
  rw [hchart]
  trivial

end LinearStudy
