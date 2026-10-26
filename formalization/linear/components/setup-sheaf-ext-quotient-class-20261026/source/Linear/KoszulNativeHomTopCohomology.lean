module
public import Linear.KoszulNativeHomTopCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- ACTUAL native Hom top homology data,constructed from the PROVED
original coefficient restriction cokernel and PROVED outgoing zero. -/
def koszulNativeHomTopHomologyData (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    ((affineKoszulNativeHomCochainComplex R N (n+1) H).sc' n (n+1) (n+2)).HomologyData :=
  ShortComplex.HomologyData.ofIsColimitCokernelCofork _
    (koszulNativeHomCochain_top_d_zero R N n H)
    (CokernelCofork.ofπ (koszulNativeHomTopRestrictionPresentation R N n H).g
      (koszulNativeHomTopRestrictionPresentation R N n H).zero)
    (koszulNativeHomTopRestrictionIsCokernel R N n H)

/-- Compute the ACTUAL native Hom cochain complex top cohomology as
ORIGINAL N/I N,using native homology rather than a substitute quotient.
No source exactness or coefficient FP/free/flat/invertibility/CM input. -/
def koszulNativeHomTopCohomologyIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulNativeHomCochainComplex R N (n+1) H).homology (n+1) ≅
      ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N))) :=
  (affineKoszulNativeHomCochainComplex R N (n+1) H).homologyIsoSc' n (n+1) (n+2)
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl)) ≪≫
      (koszulNativeHomTopHomologyData R N n H).left.homologyIso

/-- The ACTUAL top cohomology iso sends a SAME original cycle to
SAME ordered-top evaluation modulo ORIGINAL I N. This proves the
original class/restriction MORPHISM equality,not only object isomorphism. -/
theorem koszulNativeHomTopCohomologyIso_restriction (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulNativeHomCochainComplex R N (n+1) H).homologyπ (n+1) ≫
      (koszulNativeHomTopCohomologyIso R N n H).hom =
    (affineKoszulNativeHomCochainComplex R N (n+1) H).iCycles (n+1) ≫
      koszulNativeHomTopRestrictionMorphism R N n H := by
  have hc := (koszulNativeHomTopHomologyData R N n H).left.cyclesIso_hom_comp_i
  change (koszulNativeHomTopHomologyData R N n H).left.cyclesIso.hom ≫ 𝟙 _ = _ at hc
  rw [Category.comp_id] at hc
  simp only [koszulNativeHomTopCohomologyIso,Iso.trans_hom,← Category.assoc]
  rw [HomologicalComplex.π_homologyIsoSc'_hom,Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  change _ ≫ ((koszulNativeHomTopHomologyData R N n H).left.cyclesIso.hom ≫
    koszulNativeHomTopRestrictionMorphism R N n H) = _
  rw [hc,← Category.assoc,HomologicalComplex.cyclesIsoSc'_hom_iCycles]

end LinearStudy
