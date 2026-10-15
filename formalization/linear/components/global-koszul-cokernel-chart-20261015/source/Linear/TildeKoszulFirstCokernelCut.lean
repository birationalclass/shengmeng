module
public import Linear.TildeKoszulPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The ACTUAL cokernel of the original affine Koszul d1 is the SAME
original quotient-cut structure sheaf. Use the original exact presentation
and its proved epimorphism;no homology/regularity premise is added. -/
def tildeKoszulFirstCokernelOriginalCutIso (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) :
    cokernel ((tildeFunctionKoszulComplex R H).d 1 0) ≅
      (tildeKoszulPresentation R H).X₃ := by
  letI : Epi (tildeKoszulPresentation R H).g := tildeKoszulPresentation_epi R H
  exact (cokernelIsCokernel ((tildeFunctionKoszulComplex R H).d 1 0)).coconePointUniqueUpToIso
    (tildeKoszulPresentation_exact R H).gIsCokernel

/-- Retain the SAME actual quotient augmentation,not an arbitrary map. -/
theorem tildeKoszulFirstCokernelOriginalCutIso_projection (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) :
    cokernel.π ((tildeFunctionKoszulComplex R H).d 1 0) ≫
      (tildeKoszulFirstCokernelOriginalCutIso R H).hom =
      (tildeKoszulPresentation R H).g := by
  letI : Epi (tildeKoszulPresentation R H).g := tildeKoszulPresentation_epi R H
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel ((tildeFunctionKoszulComplex R H).d 1 0))
    (tildeKoszulPresentation_exact R H).gIsCokernel WalkingParallelPair.one

end LinearStudy
