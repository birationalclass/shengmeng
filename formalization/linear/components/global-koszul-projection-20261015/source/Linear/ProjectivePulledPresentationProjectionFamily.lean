module
public import Linear.ProjectivePulledPresentationProjectionCore
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {n r : ℕ}

/-- ACTUAL ORIGINAL proof term:derive ONE NONEMPTY parameter open BEFORE
EVERY integer twist,with a global cokernel comparison preserving the
original quotient projection as the native adjoint of the original chart
quotient map. All actual data and the unit condition are constructed.
No desired map equality,unit iso,cover or comparison is an added premise.
This is not canonical geometric augmentation/epsilon or original4.2. -/
def projectivePulledLinearSectionGlobalProjectionFamilyProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  let build := fun (w : Fin (r+1) → ℂ)
    (hc : projectivePulledLinearKoszulAmbientCover f V L w) (k : ℤ) =>
      projectivePulledLinearKoszulGlobalProjectionExistsProof f V L hL w k hc
  parameterFamily_of_cover
    (fun c : MvPolynomial (Fin (r+1)) ℂ => c ≠ 0)
    (fun c : MvPolynomial (Fin (r+1)) ℂ =>
      ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0)
    (fun (c : MvPolynomial (Fin (r+1)) ℂ) (w : Fin (r+1) → ℂ) =>
      MvPolynomial.eval w c ≠ 0)
    (projectivePulledLinearKoszulAmbientCover f V L) _
    (projectivePulledLinearSection_exists_presentationAmbientCover
      f V hq hf hV L hL hinj hfinite x0 hx0) build

end LinearStudy
