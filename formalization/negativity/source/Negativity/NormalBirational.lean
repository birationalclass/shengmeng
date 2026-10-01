module

public import Negativity.LocalGeometry
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic

@[expose] public section
namespace Negativity
universe u
open AlgebraicGeometry CategoryTheory

/-- The affine algebraic core of finite birational maps to a normal base.
The embedding into the base fraction field is explicit birational data;
surjectivity of the structure map is proved, not assumed. -/
theorem integral_birational_algebraMap_bijective
    (R S K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Field K] [Algebra R S] [Algebra R K]
    [IsFractionRing R K] [Algebra.IsIntegral R S]
    (j : S →ₐ[R] K) (hj : Function.Injective j) :
    Function.Bijective (algebraMap R S) := by
  constructor
  · intro a b h
    apply IsFractionRing.injective R K
    simpa using congrArg j h
  · intro b
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      ((Algebra.IsIntegral.isIntegral (R := R) b).map j)
    exact ⟨a, hj (by simpa using ha)⟩

/-- Module-finiteness supplies the integrality required by the normal-base argument. -/
theorem finite_birational_algebraMap_bijective
    (R S K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Field K] [Algebra R S] [Algebra R K]
    [IsFractionRing R K] [Module.Finite R S]
    (j : S →ₐ[R] K) (hj : Function.Injective j) :
    Function.Bijective (algebraMap R S) := by
  exact integral_birational_algebraMap_bijective R S K j hj

/-- The corresponding actual affine Scheme morphism is an isomorphism.
Passing from general normal birational Scheme data to these affine hypotheses
and gluing the affine isomorphisms are separate remaining tasks. -/
theorem finite_birational_spec_isIso
    (R S K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Field K] [Algebra R S] [Algebra R K]
    [IsFractionRing R K] [Module.Finite R S]
    (j : S →ₐ[R] K) (hj : Function.Injective j) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let e : R ≃+* S := RingEquiv.ofBijective (algebraMap R S)
    (finite_birational_algebraMap_bijective R S K j hj)
  have : IsIso (CommRingCat.ofHom (algebraMap R S)) :=
    e.toCommRingCatIso.isIso_hom
  infer_instance

end Negativity
