module
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section
namespace Negativity
open CategoryTheory
universe u v
noncomputable section
variable {R : Type u} [Ring R]
    (K : ShortComplex (ModuleCat.{v} R))
    {Q : Type v} [AddCommGroup Q] [Module R Q]

/-- A constructed cocycle-to-class map whose genuine kernel is exactly
the genuine boundary image gives the corresponding native homology
comparison. This is the existing ModuleCat quotient and first isomorphism
theorem, with no assumed homology-comparison premise. -/
def actualModuleCatHomologyQuotientComparison
    (q : K.g.hom.ker →ₗ[R] Q) (hsurj : Function.Surjective q)
    (hker : q.ker = K.moduleCatToCycles.range) :
    K.homology ≃ₗ[R] Q := by
  let e : K.moduleCatLeftHomologyData.H ≃ₗ[R] Q := by
    change (K.g.hom.ker ⧸ K.moduleCatToCycles.range) ≃ₗ[R] Q
    rw [← hker]
    exact q.quotKerEquivOfSurjective hsurj
  exact K.moduleCatHomologyIso.toLinearEquiv.trans e

#print axioms actualModuleCatHomologyQuotientComparison
end
end Negativity
