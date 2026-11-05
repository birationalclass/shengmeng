module
public import Linear.NativeProjectiveShiftedFreeCoordinateMaps
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace LinearStudy
open AlgebraicGeometry
universe u
variable {K S ι : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq ι]

/-- The actual original-prime single-coordinate and projection maps
have the Kronecker relation on actual localized modules. -/
theorem nativeShiftedFreePrime_projection_inclusion (i j : ι)
    (p : ProjectiveSpectrum 𝓑) (x : nativeProjectiveModuleAtPrime (D := S) 𝓑 p) :
    nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.proj (R := S) (φ := fun _ : ι => S) j) p
      (nativeProjectiveModuleAtPrimeMap 𝓑
        (LinearMap.single (R := S) (φ := fun _ : ι => S) i) p x) =
      if i = j then x else 0 := by
  induction x using LocalizedModule.induction_on with
  | h x den =>
    rw [nativeProjectiveModuleAtPrimeMap_mk, nativeProjectiveModuleAtPrimeMap_mk]
    by_cases hij : i = j
    · subst j
      simp only [LinearMap.proj_apply, LinearMap.single_apply, Pi.single_eq_same, ite_true]
    · simp only [LinearMap.proj_apply, LinearMap.single_apply,
        Pi.single_eq_of_ne (Ne.symm hij), ite_eq_right hij, LocalizedModule.zero_mk]

/-- The original coefficient decomposition survives actual localization
at every projective prime; finite coordinate maps sum to the identity. -/
theorem nativeShiftedFreePrime_coordinate_total [Fintype ι]
    (p : ProjectiveSpectrum 𝓑) (x : nativeProjectiveModuleAtPrime (D := ι → S) 𝓑 p) :
    (∑ i : ι, nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.single (R := S) (φ := fun _ : ι => S) i) p
        (nativeProjectiveModuleAtPrimeMap 𝓑
          (LinearMap.proj (R := S) (φ := fun _ : ι => S) i) p x)) = x := by
  induction x using LocalizedModule.induction_on with
  | h f den =>
    simp_rw [nativeProjectiveModuleAtPrimeMap_mk]
    let l := (LocalizedModule.divBy den).comp
      (LocalizedModule.mkLinearMap p.asHomogeneousIdeal.toIdeal.primeCompl (ι → S))
    have hl : ∀ y : ι → S, l y = LocalizedModule.mk y den := by
      intro y
      simp only [l, LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply,
        LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]
    change (∑ i : ι, LocalizedModule.mk (Pi.single i (f i)) den) = LocalizedModule.mk f den
    simp_rw [← hl]
    rw [← map_sum, Finset.univ_sum_single]

end LinearStudy
