module
public import Linear.NativeDualDegreeZeroChartMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
attribute [local instance] nativeCoextensionNormalizationBaseModule
attribute [local instance] nativeHomogeneousAwayModuleScalar
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The actual degree-zero chart dual comparison is injective. This
uses the original homogeneous decomposition and source-localization
universal property, not a supplied perfect chart pairing. -/
theorem finiteNativeDualDegreeZeroChartMap_injective
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    Function.Injective (finiteNativeDualDegreeZeroChartMap 𝒜 𝓑 a ha hinj) := by
  let P := Submonoid.powers a
  let Q := Localization.Away a
  let D := (ModuleCat.restrictScalars (algebraMap R S)).obj
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
  letI : Module R D := Module.compHom D (algebraMap R S)
  letI : Module Q (LocalizedModule P S) := LocalizedModule.moduleOfIsLocalization
  letI : Module Q (LocalizedModule P D) := LocalizedModule.moduleOfIsLocalization
  letI : SMul Q (LocalizedModule P S) := LocalizedModule.smulOfIsLocalization Q
  letI : SMul Q (LocalizedModule P D) := LocalizedModule.smulOfIsLocalization Q
  let E := finiteNativeCoextensionLocalizationEquiv (S := S) (Q := Q) P hinj
  intro ell₁ ell₂ h
  apply Subtype.ext
  apply E.injective
  apply (functionalSourceLocalizationRestriction_bijective (Q := Q) (M := S) P).1
  ext b
  change E ell₁.val (LocalizedModule.mk b 1) = E ell₂.val (LocalizedModule.mk b 1)
  induction b using DirectSum.Decomposition.inductionOn 𝓑 with
  | zero => simp only [LocalizedModule.zero_mk, map_zero]
  | @homogeneous d b =>
      let s : P := ⟨a^d,⟨d,rfl⟩⟩
      let y : nativeNormalizationSourceAwayZero 𝒜 𝓑 a :=
        ⟨LocalizedModule.mk (b : S) s, Submodule.subset_span ⟨d,b,b.property,rfl⟩⟩
      have hz := congrArg HomogeneousLocalization.val (LinearMap.congr_fun h y)
      have he : E ell₁.val y.val = E ell₂.val y.val := by
        simpa only [finiteNativeDualDegreeZeroChartMap_apply] using hz
      have hR : (a^d : R) • y.val = LocalizedModule.mk (b : S) 1 := by
        change (s : R) • LocalizedModule.mk (b : S) s = LocalizedModule.mk (b : S) 1
        simpa only [LocalizedModule.smul'_mk, Submonoid.smul_def] using
          LocalizedModule.mk_cancel s (b : S)
      have hQ : algebraMap R Q (a^d) • y.val = LocalizedModule.mk (b : S) 1 := by
        change algebraMap R Q (a^d) • LocalizedModule.mk (b : S) s = _
        rw [← IsLocalization.mk'_one (M := P) (S := Q) (a^d),
          LocalizedModule.mk'_smul_mk (S := P) Q]
        simpa only [one_mul, Submonoid.smul_def] using
          LocalizedModule.mk_cancel s (b : S)
      with_unfolding_all
        rw [← hQ, (E ell₁.val).map_smul, (E ell₂.val).map_smul, he]
  | add b c hb hc =>
      have hm : LocalizedModule.mk (b+c) (1 : P) =
          LocalizedModule.mk b 1 + LocalizedModule.mk c 1 :=
        (LocalizedModule.mkLinearMap P S).map_add b c
      rw [hm, map_add, map_add, hb, hc]

end LinearStudy
