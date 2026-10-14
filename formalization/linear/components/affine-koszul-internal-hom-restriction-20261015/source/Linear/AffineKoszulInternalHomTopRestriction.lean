module
public import Linear.AffineKoszulInternalDualHomDifferential
public import Linear.TildeKoszulDualTopRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- ACTUAL internal-Hom dual Koszul top presentation on ORIGINAL Spec R.
The differential is precomposition by the SAME original tilde Koszul d.
The last map is ORIGINAL coefficient restriction transported through the
CONSTRUCTED actual term-Hom iso,ending in the SAME original pushed cut. -/
def affineKoszulInternalHomTopRestrictionPresentation (R : CommRingCat.{u})
    (n : ℕ) (H : Fin (n+1) → R) : ShortComplex (Spec R).Modules where
  X₁ := schemeModuleHomModuleSheaf (tilde (ModuleCat.of R (⋀[R]^n (Fin (n+1) → R))))
    (tilde (ModuleCat.of R R))
  X₂ := schemeModuleHomModuleSheaf (tilde (ModuleCat.of R (⋀[R]^(n+1) (Fin (n+1) → R))))
    (tilde (ModuleCat.of R R))
  X₃ := (tildeKoszulDualTopRestrictionPresentation R n H).X₃
  f := schemeModuleHomPrecompose (N := tilde (ModuleCat.of R R)) ((tilde.functor R).map
    (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) n)))
  g := (affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).inv ≫
    (tildeKoszulDualTopRestrictionPresentation R n H).g
  zero := by
    have hd := affineKoszulTermInternalDualHomIso_differential R (n+1) n H
    apply (cancel_epi (affineKoszulTermTildeInternalDualHomIso R (n+1) n).hom).mp
    simp only [comp_zero]
    calc
      _ = ((affineKoszulTermTildeInternalDualHomIso R (n+1) n).hom ≫
          schemeModuleHomPrecompose (N := tilde (ModuleCat.of R R)) ((tilde.functor R).map
            (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) n)))) ≫
          (affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).inv ≫
          (tildeKoszulDualTopRestrictionPresentation R n H).g := by simp only [Category.assoc]
      _ = ((tildeKoszulDualTopRestrictionPresentation R n H).f ≫
          (affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).hom) ≫
          (affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).inv ≫
          (tildeKoszulDualTopRestrictionPresentation R n H).g := by rw [← hd];rfl
      _ = (tildeKoszulDualTopRestrictionPresentation R n H).f ≫
          (tildeKoszulDualTopRestrictionPresentation R n H).g := by
        simp only [Category.assoc,Iso.hom_inv_id_assoc]
      _ = 0 := (tildeKoszulDualTopRestrictionPresentation R n H).zero

/-- The ACTUAL internal-Hom presentation is identified with the SAME
original associated-dual presentation,using PROVED differential square. -/
def affineKoszulInternalHomTopRestrictionPresentationIso (R : CommRingCat.{u})
    (n : ℕ) (H : Fin (n+1) → R) :
    tildeKoszulDualTopRestrictionPresentation R n H ≅
      affineKoszulInternalHomTopRestrictionPresentation R n H := by
  refine ShortComplex.isoMk (affineKoszulTermTildeInternalDualHomIso R (n+1) n)
    (affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)) (Iso.refl _) ?_ ?_
  · exact (affineKoszulTermInternalDualHomIso_differential R (n+1) n H).symm
  · change (affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).hom ≫
      ((affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).inv ≫
        (tildeKoszulDualTopRestrictionPresentation R n H).g) = _
    simp only [Iso.hom_inv_id_assoc,Iso.refl_hom,Category.comp_id]

/-- ACTUAL internal-Hom dual-top sequence is exact over ANY ORIGINAL R.
No regularity,field,Noetherian or exactness certificate is assumed. -/
theorem affineKoszulInternalHomTopRestrictionPresentation_exact
    (R : CommRingCat.{u}) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulInternalHomTopRestrictionPresentation R n H).Exact :=
  ShortComplex.exact_of_iso (affineKoszulInternalHomTopRestrictionPresentationIso R n H)
    (tildeKoszulDualTopRestrictionPresentation_exact R n H)

/-- The ACTUAL original internal-Hom coefficient restriction is epi onto
ACTUAL pushed forward structure sheaf of SAME original cut Spec R/(H). -/
theorem affineKoszulInternalHomTopRestrictionPresentation_epi
    (R : CommRingCat.{u}) (n : ℕ) (H : Fin (n+1) → R) :
    Epi (affineKoszulInternalHomTopRestrictionPresentation R n H).g := by
  letI := tildeKoszulDualTopRestrictionPresentation_epi R n H
  change Epi ((affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).inv ≫
    (tildeKoszulDualTopRestrictionPresentation R n H).g)
  infer_instance

/-- The constructed ACTUAL internal-Hom restriction evaluated on the
SAME original tilde dual equals the ORIGINAL coefficient-restriction map. -/
theorem affineKoszulInternalHomTopRestrictionPresentation_restriction
    (R : CommRingCat.{u}) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).hom ≫
      (affineKoszulInternalHomTopRestrictionPresentation R n H).g =
        (tildeKoszulDualTopRestrictionPresentation R n H).g := by
  change (affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).hom ≫
    ((affineKoszulTermTildeInternalDualHomIso R (n+1) (n+1)).inv ≫ _) = _
  exact Iso.hom_inv_id_assoc _ _

end LinearStudy