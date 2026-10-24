module
public import Linear.KoszulLocalGlobalExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace LinearStudy
variable {R : Type*} [CommRing R] {n : ℕ}

/-- The actual quotient augmentation is a quasi-isomorphism when positive
Koszul exactness has been proved. No regularity hypothesis is added. -/
theorem functionKoszulAugmentation_quasiIso_of_exact
    (H : Fin n → R)
    (he : ∀ k : ℕ,0 < k → (koszulComplex (Fintype.linearCombination R H)).ExactAt k) :
    QuasiIso (functionKoszulAugmentationMap H) := by
  refine ⟨fun k => ?_⟩
  cases k with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
        ⟨functionKoszulAugmentation_exact H, ?_⟩
      · exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
          (by simp [functionKoszulAugmentationMap, ChainComplex.toSingle₀Equiv_symm_apply_f_zero])
      · apply (ModuleCat.epi_iff_surjective _).mpr
        intro v
        obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
        refine ⟨(exteriorPower.zeroEquiv R _).symm w, ?_⟩
        change Ideal.Quotient.mk _ ((exteriorPower.zeroEquiv R _)
          ((exteriorPower.zeroEquiv R _).symm w)) = _
        rw [LinearEquiv.apply_symm_apply]
    all_goals rfl
  | succ k =>
    rw [quasiIsoAt_iff_exactAt']
    · exact he (k+1) (by omega)
    · apply ChainComplex.exactAt_succ_single_obj

/-- A constructed projective resolution from the same actual exterior
complex and quotient augmentation. This definition is not a proof of its
input exactness; the projective cut application derives that exactness. -/
def functionKoszulResolutionOfExact (H : Fin n → R)
    (he : ∀ k : ℕ,0 < k → (koszulComplex (Fintype.linearCombination R H)).ExactAt k) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) where
  complex := koszulComplex (Fintype.linearCombination R H)
  projective k := ModuleCat.projective_of_free ((Pi.basisFun R (Fin n)).exteriorPower k)
  π := functionKoszulAugmentationMap H
  quasiIso := functionKoszulAugmentation_quasiIso_of_exact H he

end LinearStudy
