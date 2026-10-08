module
public import Linear.NoetherNormalizationKrull
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
universe u

/-- A finite injective normalization computes the actual transcendence
degree of the original domain, with the scalar tower constructed from g. -/
theorem finite_normalization_trdeg
    {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hfin : g.Finite) :
    Algebra.trdeg k A = (s : Cardinal) := by
  let R := MvPolynomial (Fin s) k
  letI : Algebra R A := g.toRingHom.toAlgebra
  letI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq (fun a => by
    exact (g.commutes a).symm)
  letI : Module.Finite R A := RingHom.finite_algebraMap.mp hfin
  letI : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr hinj
  have h := trdeg_add_eq k R (A := A)
  simpa [R, trdeg_eq_zero] using h.symm

/-- For an actual finite-type domain, one same integer computes both Krull
dimension and transcendence degree. No dimension formula is an input. -/
theorem finiteType_domain_exists_krull_trdeg
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ∃ s : ℕ, ringKrullDim A = (s : WithBot ℕ∞) ∧
      Algebra.trdeg k A = (s : Cardinal) := by
  obtain ⟨s, g, hinj, hfin, hdim⟩ :=
    exists_finite_normalization_krull_dimension k A
  exact ⟨s, hdim, finite_normalization_trdeg s g hinj hfin⟩

end LinearStudy
