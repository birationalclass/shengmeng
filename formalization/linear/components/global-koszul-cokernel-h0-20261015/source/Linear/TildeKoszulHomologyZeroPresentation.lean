module
public import Linear.TildeKoszulHomologyZeroCut
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- The native affine H0 comparison with its SAME original quotient
presentation as named target. This just names the proved geometric
structure-sheaf target;it does not assume a homology identification. -/
def tildeKoszulHomologyZeroPresentationIso (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) :
    (HomologicalComplex.homologyFunctor (Spec R).Modules (ComplexShape.down ℕ) 0).obj
      (tildeFunctionKoszulComplex R H) ≅ (tildeKoszulPresentation R H).X₃ := by
  exact tildeKoszulHomologyZeroOriginalCutIso R H

end LinearStudy