module
public import Linear.NativeGlobalKoszulAffineStandard
public import Linear.HomogeneousQuotientKoszulAffineCounit
import all Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K σ : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulOnAffine
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm

/-- For the SAME ORIGINAL finite homogeneous coordinate quotient,the ACTUAL
entire affine-restricted Koszul SHEAF-complex equals the native standard
Koszul on ORIGINAL H_i/a^q. No extra grading/Noetherianity/generation/QC,
source regularity/exactness or target coefficient condition is assumed. -/
def homogeneousQuotientKoszulStandardAffineIso [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    {r q : ℕ} (H : Fin r → (MvPolynomial σ K ⧸ I)) (k : ℤ) :
    letI := homogeneousQuotientGrading I hI
    (hH : ∀ i, H i ∈ homogeneousQuotientPiece I q) →
    (a : (MvPolynomial σ K ⧸ I)) → (ha : a ∈ homogeneousQuotientPiece I 1) →
    let R := CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece I) a)
    letI : (tilde.functor R).Additive :=
      AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor (R := R)
    let j := Proj.awayι (homogeneousQuotientPiece I) a ha one_pos
    nativeProjectiveKoszulOnAffine (homogeneousQuotientPiece I) R j H hH k ≅
      ((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (koszulComplex (Fintype.linearCombination
          (HomogeneousLocalization.Away (homogeneousQuotientPiece I) a)
          (fun i => HomogeneousLocalization.Away.mk (homogeneousQuotientPiece I)
            ha q (H i) (by simpa using hH i)))) := by
  letI := homogeneousQuotientGrading I hI
  intro hH a ha
  exact nativeProjectiveKoszulStandardAffineIso (homogeneousQuotientPiece I)
    (fun i : σ => Ideal.Quotient.mk I (MvPolynomial.X i))
    (fun i => ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X K i,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top I) H hH k a ha

end LinearStudy
