module
public import Linear.HomogeneousPrimeQuotientActualSerre
public import Linear.SchemeModuleActualHBoundGlobalUnitExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] nativeProjectiveModuleSheaf homogeneousQuotientGrading
/-- The ORIGINAL integral homogeneous quotient has ONE positive bound for all
later integer twists and all positive GLOBAL unit Ext degrees.The SAME actual
source Serre bound and canonical Ext/H map discharge every geometric premise. -/
theorem homogeneousPrimeQuotient_globalUnitExtSerreBound
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) [I.IsPrime] (j : σ) :
    letI := homogeneousQuotientGrading I hI
    let B := homogeneousQuotientPiece I
    let G := nativeProjectiveRingIntegerPiece B
    ∃ N : ℕ,0 < N ∧ ∀ k : ℤ,(N : ℤ) ≤ k → ∀ i : ℕ,0 < i →
      Subsingleton (Ext.{u} (SheafOfModules.unit (Proj B).ringCatSheaf)
        (nativeProjectiveModuleSheaf B G (nativeProjectiveRingIntegerPiece_graded B) k) i) := by
  letI := homogeneousQuotientGrading I hI
  let B := homogeneousQuotientPiece I
  let G := nativeProjectiveRingIntegerPiece B
  let F := fun k => nativeProjectiveModuleSheaf B G (nativeProjectiveRingIntegerPiece_graded B) k
  obtain ⟨b,hb⟩ := homogeneousPrimeQuotient_eventually_allInteger_actualHigherH_vanish I hI j
  have hH : ∀ k : ℤ,((b+1 : ℕ) : ℤ) ≤ k → ∀ q : ℕ,
      Subsingleton (schemeModuleActualCohomology (Proj B) (F k) (q+1)) :=
    fun k hk q => hb k (by omega) q
  exact ⟨b+1,by omega,schemeModuleActualHBound_globalUnitExtBound (Proj B) F (b+1) hH⟩
end LinearStudy
