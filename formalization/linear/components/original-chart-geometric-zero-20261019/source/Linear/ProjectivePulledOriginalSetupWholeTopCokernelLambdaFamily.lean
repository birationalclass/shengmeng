module
public import Linear.ParameterPolynomialFamilyIntersection
public import Linear.ProjectivePulledOriginalSetupWholeTopCokernelFamily
public import Linear.ProjectivePulledWholeCokernelLambdaFamily
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local irreducible] projectivePulledOriginalWholeTopCokernelStatement
  projectivePulledOriginalCokernelLambdaStatement
variable {n r : ℕ}
/-- ORIGINAL Setup derives ONE NONEMPTY parameter open BEFORE ALL integer k.
For the SAME original quotient augmentation e,he and original top functional,
retain the proved WHOLE highest-Hom-cokernel class family, while proving
bijectivity of the SAME canonical lambda on the actual original d1-cokernel
for ALL actual coefficient sheaves and positive Ext degrees on that common
open. This does not prove the local a|S formula, theta4.1 or uniform m. -/
def projectivePulledOriginalSetupWholeTopCokernelLambdaFamilyProof
    (hr : 0 < r)
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  parameterPolynomialFamily_intersection
    (projectivePulledOriginalSetupWholeTopCokernelFamilyProof
      hr f V hrn hq hf hV L hL hinj hfinite x0 hx0)
    (projectivePulledLinearSection_exists_originalCokernelCanonicalLambda_bijective
      f V hq hf hV L hL hinj hfinite x0 hx0)
end LinearStudy

