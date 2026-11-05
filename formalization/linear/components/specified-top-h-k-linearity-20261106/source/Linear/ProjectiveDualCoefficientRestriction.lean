module
public import Linear.ProjectiveGradedDualCoefficientEquiv
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory
variable {R S : Type} [CommRing R] [CommRing S] {σ : Type}
attribute [local instance] projectiveCoefficientInverseForward projectiveCoefficientInverseBackward

/-- The constructed ORIGINAL dual coefficient equivalence is an actual
R-linear categorical isomorphism to the ORIGINAL restriction of scalars.
Uses mathlib semilinearMapAddEquiv and the proved original bijectivity. -/
def projectiveHomogeneousDualCoefficientIso (e : R ≃+* S) (m : ℕ) :
    ModuleCat.of R (Module.Dual R (homogeneousSubmodule σ R m)) ≅
      (ModuleCat.restrictScalars e.toRingHom).obj
        (ModuleCat.of S (Module.Dual S (homogeneousSubmodule σ S m))) := by
  let f := ModuleCat.semilinearMapAddEquiv e.toRingHom
    (ModuleCat.of R (Module.Dual R (homogeneousSubmodule σ R m)))
    (ModuleCat.of S (Module.Dual S (homogeneousSubmodule σ S m)))
    (projectiveHomogeneousDualCoefficientEquiv e m).toLinearMap
  haveI : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr
    (projectiveHomogeneousDualCoefficientEquiv e m).bijective
  exact asIso f

/-- The categorical isomorphism is the same ORIGINAL dual coefficient
map,not a independently chosen abstract module isomorphism. -/
theorem projectiveHomogeneousDualCoefficientIso_hom_apply (e : R ≃+* S) (m : ℕ)
    (φ : Module.Dual R (homogeneousSubmodule σ R m)) :
    (projectiveHomogeneousDualCoefficientIso e m).hom φ =
      projectiveHomogeneousDualCoefficientEquiv e m φ := rfl

/-- The ACTUAL graded polynomial dual entry square holds in ModuleCat R
under ORIGINAL scalar restriction,including negative-degree zero entries. -/
theorem projectiveHomogeneousDualCoefficientIso_gradedEntry (e : R ≃+* S)
    (a b : ℕ) (p : homogeneousSubmodule σ R (a-b)) :
    projectiveHomogeneousGradedPolynomialDualEntry a b p ≫
        (projectiveHomogeneousDualCoefficientIso e b).hom =
      (projectiveHomogeneousDualCoefficientIso e a).hom ≫
        (ModuleCat.restrictScalars e.toRingHom).map
          (projectiveHomogeneousGradedPolynomialDualEntry a b
            (projectiveHomogeneousCoefficientEquiv e (a-b) p)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact projectiveHomogeneousDualCoefficientEquiv_gradedEntry e a b p φ

/-- The ACTUAL canonical specialization uses Scheme.GammaSpecIso; no
ring,dual or scalar-restriction comparison is supplied as an input. -/
def coordinateCanonicalHomogeneousDualCoefficientIso (K : Type) [CommRing K] (m : ℕ) :
    ModuleCat.of K (Module.Dual K (homogeneousSubmodule σ K m)) ≅
      (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
        (ModuleCat.of (coordinateCanonicalBaseRing K)
          (Module.Dual (coordinateCanonicalBaseRing K)
            (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) m))) :=
  projectiveHomogeneousDualCoefficientIso (coordinateCanonicalCoefficientRingEquiv K) m

/-- The categorical canonical scalar comparison respects each ORIGINAL
graded entry with its ACTUAL degree casts and negative zero branch. -/
theorem coordinateCanonicalHomogeneousDualCoefficientIso_gradedEntry
    (K : Type) [CommRing K] (a b : ℕ) (p : homogeneousSubmodule σ K (a-b)) :
    projectiveHomogeneousGradedPolynomialDualEntry a b p ≫
        (coordinateCanonicalHomogeneousDualCoefficientIso K b).hom =
      (coordinateCanonicalHomogeneousDualCoefficientIso K a).hom ≫
        (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
          (projectiveHomogeneousGradedPolynomialDualEntry a b
            (coordinateCanonicalHomogeneousCoefficientEquiv K (a-b) p)) :=
  projectiveHomogeneousDualCoefficientIso_gradedEntry
    (coordinateCanonicalCoefficientRingEquiv K) a b p

end MvPolynomial
