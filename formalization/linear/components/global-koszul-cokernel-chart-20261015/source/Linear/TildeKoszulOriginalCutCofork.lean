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

/-- The ACTUAL original affine quotient augmentation,as a native cokernel
cofork for the SAME original sheaf Koszul d1. No quotient target is supplied. -/
def tildeKoszulOriginalCutCokernelCofork (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) : CokernelCofork ((tildeFunctionKoszulComplex R H).d 1 0) :=
  CokernelCofork.ofπ (tildeKoszulPresentation R H).g (tildeKoszulPresentation R H).zero

/-- Its point is EXACTLY the original quotient-cut structure sheaf pushed
forward,with the original ideal and nilpotents retained. -/
theorem tildeKoszulOriginalCutCokernelCofork_point (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) :
    (tildeKoszulOriginalCutCokernelCofork R H).pt =
      (Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
          (SheafOfModules.unit.{u}
            (Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range H)))).ringCatSheaf) := rfl

/-- Its projection is the SAME actual original quotient augmentation. -/
theorem tildeKoszulOriginalCutCokernelCofork_projection (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) :
    (tildeKoszulOriginalCutCokernelCofork R H).π = (tildeKoszulPresentation R H).g := rfl

/-- PROVE the universal property from actual original presentation
exactness and its proved epi;no universal-property premise is added. -/
def tildeKoszulOriginalCutCokernelCoforkIsColimit (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) : IsColimit (tildeKoszulOriginalCutCokernelCofork R H) := by
  letI : Epi (tildeKoszulPresentation R H).g := tildeKoszulPresentation_epi R H
  exact (tildeKoszulPresentation_exact R H).gIsCokernel

end LinearStudy