module
public import Linear.NativeCoextensionUpperLocalizationEquiv
public import Linear.ProjectiveFiniteDualFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] LocalizedModule.moduleOfIsLocalization
variable {n r : ℕ}

/-- At each ORIGINAL normalization coordinate, the original native dual
localized over the original coordinate ring is the actual native dual of
the localized normalization. The comparison is linear over that localized
coordinate ring. This is not yet the degree-zero projective chart dual or
the canonical-sheaf identification. -/
def projectiveNormalizationNativeDualCoordinateLocalizationEquiv
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    let P := Submonoid.powers (MvPolynomial.X i : A)
    let Q := Localization P
    let B' := LocalizedModule P B
    letI : Module Q B' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q B' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    letI : Algebra B B' := nativeLocalizedUpperAlgebra P
    letI : IsLocalization (Algebra.algebraMapSubmonoid B P) B' :=
      nativeLocalizedUpperAlgebra_isLocalization P
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    letI : Module B' (LocalizedModule (Algebra.algebraMapSubmonoid B P) D) :=
      LocalizedModule.moduleOfIsLocalization
    LocalizedModule (Algebra.algebraMapSubmonoid B P) D ≃ₗ[B']
      ((ModuleCat.coextendScalars (algebraMap Q B')).obj (ModuleCat.of Q Q)) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Module.Finite A B := hfinite
  let P := Submonoid.powers (MvPolynomial.X i : A)
  let Q := Localization P
  let B' := LocalizedModule P B
  letI : Module Q B' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q B' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  letI : Algebra B B' := nativeLocalizedUpperAlgebra P
  letI : IsLocalization (Algebra.algebraMapSubmonoid B P) B' :=
    nativeLocalizedUpperAlgebra_isLocalization P
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  letI : Module B' (LocalizedModule (Algebra.algebraMapSubmonoid B P) D) :=
    LocalizedModule.moduleOfIsLocalization
  dsimp only
  with_unfolding_all exact (finiteNativeCoextensionUpperLocalizationEquiv
    (R := A) (S := B) (Q := Q) P
      (IsLocalization.injective Q
        (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))))

/-- The ORIGINAL upper-ring linear normalization comparison preserves
the value of each original functional at each original algebra element. -/
theorem projectiveNormalizationNativeDualCoordinateLocalizationEquiv_apply_original
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    let P := Submonoid.powers (MvPolynomial.X i : A)
    let Q := Localization P
    let B' := LocalizedModule P B
    letI : Module Q B' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q B' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    letI : Algebra B B' := nativeLocalizedUpperAlgebra P
    letI : IsLocalization (Algebra.algebraMapSubmonoid B P) B' :=
      nativeLocalizedUpperAlgebra_isLocalization P
    ∀ ell : (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A), ∀ x : B,
      nativeCoextensionOriginalDualEquiv (R := Q) (S := B')
        (projectiveNormalizationNativeDualCoordinateLocalizationEquiv V L hfinite i
          (LocalizedModule.mk ell 1)) (LocalizedModule.mk x 1) =
        algebraMap A Q (nativeCoextensionOriginalDualEquiv (R := A) (S := B) ell x) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Module.Finite A B := hfinite
  let P := Submonoid.powers (MvPolynomial.X i : A)
  let Q := Localization P
  let B' := LocalizedModule P B
  letI : Module Q B' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q B' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  letI : Algebra B B' := nativeLocalizedUpperAlgebra P
  letI : IsLocalization (Algebra.algebraMapSubmonoid B P) B' :=
    nativeLocalizedUpperAlgebra_isLocalization P
  dsimp only
  intro ell x
  with_unfolding_all exact (finiteNativeCoextensionUpperLocalizationEquiv_apply_original
    (R := A) (S := B) (Q := Q) P
      (IsLocalization.injective Q
        (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))) ell x)

end LinearStudy
