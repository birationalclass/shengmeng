module
public import Linear.ProjectiveFiniteDualTorsionFree
public import Linear.FiniteCoextensionModule
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory
variable {n r : ℕ}

/-- The native dual of the actual original finite linear normalization
is a finite module over its actual polynomial base. This is algebraic
support for the canonical-sheaf construction, not that identification. -/
theorem projectiveLinearNormalization_finiteDual_finite
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    Module.Finite (MvPolynomial (Fin (r+1)) ℂ)
      ((ModuleCat.restrictScalars (projectiveLinearNormalizationMap V L).toRingHom).obj
        ((ModuleCat.coextendScalars (projectiveLinearNormalizationMap V L).toRingHom).obj
          (ModuleCat.of (MvPolynomial (Fin (r+1)) ℂ) (MvPolynomial (Fin (r+1)) ℂ)))) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Module.Finite A B := hfinite
  exact restrictedCoextensionDual_finite (R := A) (S := B)

/-- Construct the original normalization and prove finiteness and
torsion-freeness of its actual dual, instead of supplying a normalization
or those dual-module properties as additional inputs. -/
theorem projective_exists_linear_normalization_with_finiteDual
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        Module.Finite (MvPolynomial (Fin (r+1)) ℂ)
          ((ModuleCat.restrictScalars (projectiveLinearNormalizationMap V L).toRingHom).obj
            ((ModuleCat.coextendScalars (projectiveLinearNormalizationMap V L).toRingHom).obj
              (ModuleCat.of (MvPolynomial (Fin (r+1)) ℂ) (MvPolynomial (Fin (r+1)) ℂ)))) ∧
        ∀ b : CoordinateRing n ⧸ V.ideal.toIdeal,
          ∀ ell : (ModuleCat.coextendScalars (projectiveLinearNormalizationMap V L).toRingHom).obj
            (ModuleCat.of (MvPolynomial (Fin (r+1)) ℂ) (MvPolynomial (Fin (r+1)) ℂ)),
          b • ell = 0 → b = 0 ∨ ell = 0 := by
  obtain ⟨r,hr,hdim,L,hL,hinj,hfinite,_⟩ :=
    projective_exists_linear_normalization_chart_dimension V x hx
  exact ⟨r,hr,hdim,L,hL,hinj,hfinite,
    projectiveLinearNormalization_finiteDual_finite V L hfinite,
    projectiveLinearNormalization_finiteDual_smul_eq_zero V L hfinite⟩

end LinearStudy
