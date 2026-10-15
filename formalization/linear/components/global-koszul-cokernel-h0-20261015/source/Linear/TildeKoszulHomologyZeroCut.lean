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

/-- H0 of the SAME actual native affine Koszul SHEAF complex is the
structure sheaf of the ACTUAL original cut pushed forward. Reuse the
existing exact original quotient presentation and its proved epimorphism,
and native cokernel uniqueness. NO source regularity/exactness is assumed. -/
def tildeKoszulHomologyZeroOriginalCutIso (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) :
    (tildeFunctionKoszulComplex R H).homology 0 ≅
      (Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
          (SheafOfModules.unit.{u}
            (Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range H)))).ringCatSheaf) := by
  let C := tildeFunctionKoszulComplex R H
  letI : Epi (tildeKoszulPresentation R H).g := tildeKoszulPresentation_epi R H
  exact C.isoHomologyι₀ ≪≫
    (C.opcyclesIsCokernel 1 0 (by simp)).coconePointUniqueUpToIso
      (tildeKoszulPresentation_exact R H).gIsCokernel

end LinearStudy