module
public import Linear.AffineKoszulInternalHomCochain
public import Linear.TildeKoszulHomCoefficientRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- ACTUAL native Hom top term maps by the SAME original ordered-top
coefficient restriction,not by an assumed cokernel identification. -/
def koszulNativeHomTopRestrictionMorphism (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulNativeHomCochainComplex R N (n+1) H).X (n+1) ⟶
      ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N))) :=
  (affineKoszulNativeHomCochainTermIso R N (n+1) (n+1) H).hom ≫
    ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)

attribute [local irreducible] affineKoszulNativeHomCochainTermIso

/-- ORIGINAL native incoming differential is killed by ORIGINAL restriction. -/
theorem koszulNativeHomTopRestrictionMorphism_comp (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulNativeHomCochainComplex R N (n+1) H).d n (n+1) ≫
      koszulNativeHomTopRestrictionMorphism R N n H = 0 := by
  have hd := affineKoszulNativeHomCochainTermIso_d R N (n+1) H n (n+1)
  rw [koszulComplex.d_eq_d,ModuleCat.hom_ofHom] at hd
  rw [koszulNativeHomTopRestrictionMorphism,← Category.assoc,hd,Category.assoc]
  have hz : ModuleCat.ofHom
      (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n)) ≫
      ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H) = 0 :=
    ModuleCat.hom_ext (koszulTopHomCoefficientRestriction_comp R N n H)
  rw [hz,comp_zero]

/-- SAME ACTUAL native Hom differential and restriction form a short complex. -/
def koszulNativeHomTopRestrictionPresentation (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) : ShortComplex (ModuleCat.{u} R) where
  X₁ := (affineKoszulNativeHomCochainComplex R N (n+1) H).X n
  X₂ := (affineKoszulNativeHomCochainComplex R N (n+1) H).X (n+1)
  X₃ := ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)))
  f := (affineKoszulNativeHomCochainComplex R N (n+1) H).d n (n+1)
  g := koszulNativeHomTopRestrictionMorphism R N n H
  zero := koszulNativeHomTopRestrictionMorphism_comp R N n H

/-- Actual native categorical/linear Hom maps identify the SAME original
short complex with the already PROVED original coefficient presentation. -/
def koszulNativeHomTopRestrictionPresentationIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    koszulNativeHomTopRestrictionPresentation R N n H ≅
      koszulHomCoefficientRestrictionModulePresentation R N n H := by
  refine ShortComplex.isoMk
    (affineKoszulNativeHomCochainTermIso R N (n+1) n H)
    (affineKoszulNativeHomCochainTermIso R N (n+1) (n+1) H) (Iso.refl _) ?_ ?_
  · have hd := affineKoszulNativeHomCochainTermIso_d R N (n+1) H n (n+1)
    rw [koszulComplex.d_eq_d,ModuleCat.hom_ofHom] at hd
    exact hd.symm
  · simp only [koszulNativeHomTopRestrictionPresentation,
      koszulNativeHomTopRestrictionMorphism,koszulHomCoefficientRestrictionModulePresentation,
      Iso.refl_hom,Category.comp_id]

/-- Exactness derives from the actual original image/kernel proof;it is
not an extra premise on the source equations or on the coefficient N. -/
theorem koszulNativeHomTopRestrictionPresentation_exact (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (koszulNativeHomTopRestrictionPresentation R N n H).Exact :=
  ShortComplex.exact_of_iso (koszulNativeHomTopRestrictionPresentationIso R N n H).symm
    (koszulHomCoefficientRestrictionModulePresentation_exact R N n H)

/-- SAME original restriction is epi for arbitrary ORIGINAL N. -/
theorem koszulNativeHomTopRestrictionPresentation_epi (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    Epi (koszulNativeHomTopRestrictionPresentation R N n H).g := by
  have hρ : Epi (ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)) :=
    (ModuleCat.epi_iff_surjective _).mpr (koszulTopHomCoefficientRestriction_surjective n H)
  change Epi ((affineKoszulNativeHomCochainTermIso R N (n+1) (n+1) H).hom ≫ _)
  infer_instance

/-- The ACTUAL outgoing term is ZERO because original exterior degree
exceeds the original number of equations;N is completely arbitrary. -/
theorem koszulNativeHomCochain_next_isZero (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    IsZero ((affineKoszulNativeHomCochainComplex R N (n+1) H).X (n+2)) := by
  have hK : IsZero ((koszulComplex (Fintype.linearCombination R H)).X (n+2)) :=
    koszulComplex.isZero_X_of_card_generators_lt _
      (Pi.basisFun R (Fin (n+1))) (Pi.basisFun R (Fin (n+1))).span_eq (n+2) (by simp)
  letI : Subsingleton ((affineKoszulNativeHomCochainComplex R N (n+1) H).X (n+2)) :=
    ⟨fun f g => hK.eq_of_src f g⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- SAME original top outgoing differential is ZERO,without a certificate. -/
theorem koszulNativeHomCochain_top_d_zero (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulNativeHomCochainComplex R N (n+1) H).d (n+1) (n+2) = 0 :=
  (koszulNativeHomCochain_next_isZero R N n H).eq_of_tgt _ _

/-- Original coefficient quotient is an ACTUAL categorical cokernel of
SAME original native incoming Hom differential. No desired colimit input. -/
def koszulNativeHomTopRestrictionIsCokernel (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    IsColimit (CokernelCofork.ofπ (koszulNativeHomTopRestrictionPresentation R N n H).g
      (koszulNativeHomTopRestrictionPresentation R N n H).zero) := by
  letI := koszulNativeHomTopRestrictionPresentation_epi R N n H
  exact (koszulNativeHomTopRestrictionPresentation_exact R N n H).gIsCokernel

end LinearStudy
