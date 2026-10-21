module
public import Linear.ProjectiveConeSurjectivity
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The actual homogeneous coordinate-domain endomorphism induced by f. -/
def projectiveCoordinateDomainMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    (CoordinateRing n ⧸ V.ideal.toIdeal) →ₐ[ℂ] (CoordinateRing n ⧸ V.ideal.toIdeal) where
  toRingHom := Ideal.quotientMap V.ideal.toIdeal (MvPolynomial.aeval f.forms).toRingHom
    (le_of_eq (projective_surjective_invariant_pullback_comap f V hq hf hV).symm)
  commutes' := by
    intro a
    change Ideal.quotientMap V.ideal.toIdeal (MvPolynomial.aeval f.forms).toRingHom _
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.C a)) =
        Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.C a)
    rw [Ideal.quotientMap_mk]
    simp

theorem projectiveCoordinateDomainMap_mk
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (H : CoordinateRing n) :
    projectiveCoordinateDomainMap f V hq hf hV (Ideal.Quotient.mk V.ideal.toIdeal H) =
      Ideal.Quotient.mk V.ideal.toIdeal ((MvPolynomial.aeval f.forms) H) := by
  exact Ideal.quotientMap_mk (H :=
    le_of_eq (projective_surjective_invariant_pullback_comap f V hq hf hV).symm)

theorem projectiveCoordinateDomainMap_injective
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    Function.Injective (projectiveCoordinateDomainMap f V hq hf hV) := by
  unfold projectiveCoordinateDomainMap
  exact Ideal.quotientMap_injective'
    (H := le_of_eq (projective_surjective_invariant_pullback_comap f V hq hf hV).symm)
    (le_of_eq (projective_surjective_invariant_pullback_comap f V hq hf hV))

end LinearStudy
