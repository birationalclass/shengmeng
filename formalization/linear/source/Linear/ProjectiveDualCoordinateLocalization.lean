module
public import Linear.FiniteNativeCoextensionLocalization
public import Linear.ProjectiveFiniteDualFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] LocalizedModule.moduleOfIsLocalization
variable {n r : ℕ}

/-- On each original normalization coordinate, localize the ACTUAL native
dual and compare it with the actual localized-source dual. This is an
algebraic localization comparison; the degree-zero projective chart
and canonical-sheaf identification are separate obligations. -/
def projectiveNormalizationDualCoordinateLocalizationEquiv
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    let P := Submonoid.powers (MvPolynomial.X i : A)
    let Q := Localization P
    let D := (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A))
    letI : Module Q (LocalizedModule P B) := LocalizedModule.moduleOfIsLocalization
    letI : Module Q (LocalizedModule P D) := LocalizedModule.moduleOfIsLocalization
    LocalizedModule P D ≃ₗ[Q] (LocalizedModule P B →ₗ[Q] Q) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : Module.Finite A B := hfinite
  let P := Submonoid.powers (MvPolynomial.X i : A)
  let Q := Localization P
  let D := (ModuleCat.restrictScalars (algebraMap A B)).obj
    ((ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A))
  letI : Module Q (LocalizedModule P B) := LocalizedModule.moduleOfIsLocalization
  letI : Module Q (LocalizedModule P D) := LocalizedModule.moduleOfIsLocalization
  have hinj : Function.Injective (algebraMap A Q) :=
    IsLocalization.injective Q
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))
  dsimp only
  with_unfolding_all
    exact finiteNativeCoextensionLocalizationEquiv (R := A) (S := B) (Q := Q) P hinj

/-- The ORIGINAL normalization comparison preserves evaluation on every
original algebra element, before introducing fractions in either argument. -/
theorem projectiveNormalizationDualCoordinateLocalizationEquiv_apply_original
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    let P := Submonoid.powers (MvPolynomial.X i : A)
    let Q := Localization P
    let D := (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A))
    letI : Module Q (LocalizedModule P B) := LocalizedModule.moduleOfIsLocalization
    letI : Module Q (LocalizedModule P D) := LocalizedModule.moduleOfIsLocalization
    ∀ ell : D, ∀ x : B,
      projectiveNormalizationDualCoordinateLocalizationEquiv V L hfinite i
        (LocalizedModule.mk ell 1) (LocalizedModule.mk x 1) =
          algebraMap A Q (nativeCoextensionOriginalDualEquiv (R := A) (S := B) ell x) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : Module.Finite A B := hfinite
  let P := Submonoid.powers (MvPolynomial.X i : A)
  let Q := Localization P
  let D := (ModuleCat.restrictScalars (algebraMap A B)).obj
    ((ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A))
  letI : Module Q (LocalizedModule P B) := LocalizedModule.moduleOfIsLocalization
  letI : Module Q (LocalizedModule P D) := LocalizedModule.moduleOfIsLocalization
  dsimp only
  intro ell x
  with_unfolding_all
    exact finiteNativeCoextensionLocalizationEquiv_apply_mk (R := A) (S := B) (Q := Q) P
      (IsLocalization.injective Q
        (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))) ell x

end LinearStudy
