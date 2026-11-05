module
public import Linear.NativeLocalizedUpperAlgebra
public import Linear.NativeDualDegreeZeroSpanValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The original base-module localization is the original upper-ring
localization at the image of the chosen normalization coordinate. -/
theorem nativeNormalizationFullChart_isLocalization (a : R) :
    letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
    IsLocalization (Submonoid.powers (algebraMap R S a))
      (LocalizedModule (Submonoid.powers a) S) := by
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
    nativeLocalizedUpperAlgebra_isLocalization (S := S) (Submonoid.powers a)

/-- Compare the ACTUAL full source localization with the full localization
of the original source ring at the original coordinate image. -/
def nativeNormalizationFullChartEquiv (a : R) :
    letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
    LocalizedModule (Submonoid.powers a) S ≃ₐ[S]
      Localization.Away (algebraMap R S a) := by
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  letI := nativeNormalizationFullChart_isLocalization (S := S) a
  exact IsLocalization.algEquiv (Submonoid.powers (algebraMap R S a))
    (LocalizedModule (Submonoid.powers a) S) (Localization.Away (algebraMap R S a))

/-- The comparison retains original numerators at denominator one. -/
theorem nativeNormalizationFullChartEquiv_numerator (a : R) (b : S) :
    nativeNormalizationFullChartEquiv (S := S) a (LocalizedModule.mk b 1) =
      algebraMap S (Localization.Away (algebraMap R S a)) b := by
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  exact (nativeNormalizationFullChartEquiv (S := S) a).commutes b

/-- The full comparison preserves the actual fraction with the image of
the original denominator. -/
theorem nativeNormalizationFullChartEquiv_mk
    (a : R) (b : S) (s : Submonoid.powers a) :
    nativeNormalizationFullChartEquiv (S := S) a (LocalizedModule.mk b s) =
      IsLocalization.mk' (M := Submonoid.powers (algebraMap R S a))
        (Localization.Away (algebraMap R S a)) b
        ⟨algebraMap R S s, by
          obtain ⟨n,hn⟩ := s.property
          exact ⟨n, by simpa only [map_pow] using congrArg (algebraMap R S) hn⟩⟩ := by
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  letI := nativeNormalizationFullChart_isLocalization (S := S) a
  let s' : Submonoid.powers (algebraMap R S a) :=
    ⟨algebraMap R S s, by
      obtain ⟨n,hn⟩ := s.property
      exact ⟨n, by simpa only [map_pow] using congrArg (algebraMap R S) hn⟩⟩
  have hm : LocalizedModule.mk b s =
      IsLocalization.mk' (M := Submonoid.powers (algebraMap R S a))
        (LocalizedModule (Submonoid.powers a) S) b s' := by
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    change LocalizedModule.mk b s * LocalizedModule.mk (algebraMap R S s) 1 =
      LocalizedModule.mk b 1
    rw [LocalizedModule.mk_mul_mk, mul_one, mul_comm b (algebraMap R S s)]
    simpa only [Submonoid.smul_def, Algebra.smul_def] using LocalizedModule.mk_cancel s b
  change IsLocalization.algEquiv (Submonoid.powers (algebraMap R S a))
    (LocalizedModule (Submonoid.powers a) S) (Localization.Away (algebraMap R S a))
      (LocalizedModule.mk b s) = _
  rw [hm, IsLocalization.algEquiv_mk']

end LinearStudy
