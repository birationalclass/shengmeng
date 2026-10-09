module
public import Linear.FiniteCoextensionTorsionFree
public import Linear.ProjectiveLinearNormalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory
variable {n r : ℕ}

/-- The actual dual from an original finite linear normalization is
torsion-free over the original homogeneous coordinate ring. No canonical
sheaf identification is assumed or claimed here. -/
theorem projectiveLinearNormalization_finiteDual_smul_eq_zero
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (b : CoordinateRing n ⧸ V.ideal.toIdeal)
    (ell : (ModuleCat.coextendScalars (projectiveLinearNormalizationMap V L).toRingHom).obj
      (ModuleCat.of (MvPolynomial (Fin (r+1)) ℂ) (MvPolynomial (Fin (r+1)) ℂ)))
    (h : b • ell = 0) : b = 0 ∨ ell = 0 := by
  letI := V.prime
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Module.Finite A B := hfinite
  letI : Algebra.IsAlgebraic A B := inferInstance
  exact coextension_smul_eq_zero (R := A) (S := B) b ell h

end LinearStudy
