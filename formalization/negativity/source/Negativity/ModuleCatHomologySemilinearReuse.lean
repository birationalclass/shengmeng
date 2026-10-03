module
public import Negativity.ModuleCatHomologyQuotientReuse
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section
namespace Negativity
open CategoryTheory
universe u v
noncomputable section
variable {R S : Type u} [Ring R] [Ring S]
    (K : ShortComplex (ModuleCat.{v} R))
    (σ : R →+* S) {Q : Type v} [AddCommGroup Q] [Module S Q]

/-- Actual native homology maps to the target classes by an actual
semilinear cocycle map killing the actual boundary image. -/
def actualModuleCatHomologySemilinearQuotientMap
    (q : K.g.hom.ker →ₛₗ[σ] Q)
    (hboundary : K.moduleCatToCycles.range ≤ q.ker) :
    K.homology →ₛₗ[σ] Q :=
  (K.moduleCatToCycles.range.liftQ q hboundary).comp
    K.moduleCatHomologyIso.hom.hom

theorem actual_module_cat_homology_semilinear_quotient_map_bijective
    (q : K.g.hom.ker →ₛₗ[σ] Q) (hsurj : Function.Surjective q)
    (hker : q.ker = K.moduleCatToCycles.range) :
    Function.Bijective (actualModuleCatHomologySemilinearQuotientMap K σ q hker.ge) := by
  let l := K.moduleCatToCycles.range.liftQ q hker.ge
  have hl : Function.Bijective l := by
    constructor
    · apply (LinearMap.ker_eq_bot).mp
      exact Submodule.ker_liftQ_eq_bot _ q hker.ge hker.le
    · intro y
      obtain ⟨a, rfl⟩ := hsurj y
      exact ⟨Submodule.Quotient.mk a, rfl⟩
  exact hl.comp K.moduleCatHomologyIso.toLinearEquiv.bijective

theorem actual_module_cat_homology_finite_of_semilinear_quotient
    [RingHomSurjective σ] [Module.Finite R K.homology]
    (q : K.g.hom.ker →ₛₗ[σ] Q) (hsurj : Function.Surjective q)
    (hker : q.ker = K.moduleCatToCycles.range) :
    Module.Finite S Q :=
  (LinearMap.finite_iff_of_bijective
    (actualModuleCatHomologySemilinearQuotientMap K σ q hker.ge)
    (actual_module_cat_homology_semilinear_quotient_map_bijective K σ q hsurj hker)).mp
      inferInstance

#print axioms actualModuleCatHomologySemilinearQuotientMap
#print axioms actual_module_cat_homology_finite_of_semilinear_quotient
end
end Negativity
