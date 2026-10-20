module
public import Linear.HomogeneousPrimeQuotientActualGlobalUnitExt
public import Linear.Projective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] nativeProjectiveModuleSheaf homogeneousQuotientGrading
/-- ONE positive bound for the ORIGINAL V precedes ALL later INTEGER twists
and ALL positive ACTUAL native sheaf-H degrees.No CM,smoothness,canonical
identification or desired-vanishing hypothesis is added. -/
theorem originalProjectiveStructureTwist_actualSerreBound {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    let G := nativeProjectiveRingIntegerPiece B
    ∃ N : ℕ,0 < N ∧ ∀ k : ℤ,(N : ℤ) ≤ k → ∀ q : ℕ,
      Subsingleton (schemeModuleActualCohomology (Proj B)
        (nativeProjectiveModuleSheaf B G (nativeProjectiveRingIntegerPiece_graded B) k) (q+1)) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : V.ideal.toIdeal.IsPrime := V.prime
  obtain ⟨b,hb⟩ := homogeneousPrimeQuotient_eventually_allInteger_actualHigherH_vanish
    V.ideal.toIdeal V.ideal.isHomogeneous (0 : Fin (n+1))
  exact ⟨b+1,by omega,fun k hk q => hb k (by omega) q⟩
/-- The SAME original-V geometry proves a positive global structure-unit Ext
Serre bound before ALL later integer twists and ALL positive Ext degrees.
This closes the geometric premise,not original4.1/4.2 or the main theorem. -/
theorem originalProjectiveStructureTwist_globalUnitExtSerreBound {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    let G := nativeProjectiveRingIntegerPiece B
    ∃ N : ℕ,0 < N ∧ ∀ k : ℤ,(N : ℤ) ≤ k → ∀ i : ℕ,0 < i →
      Subsingleton (Ext.{0} (SheafOfModules.unit (Proj B).ringCatSheaf)
        (nativeProjectiveModuleSheaf B G (nativeProjectiveRingIntegerPiece_graded B) k) i) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : V.ideal.toIdeal.IsPrime := V.prime
  exact homogeneousPrimeQuotient_globalUnitExtSerreBound
    V.ideal.toIdeal V.ideal.isHomogeneous (0 : Fin (n+1))
end LinearStudy
