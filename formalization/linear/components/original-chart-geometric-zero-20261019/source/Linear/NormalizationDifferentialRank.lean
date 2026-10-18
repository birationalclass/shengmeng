module
public import Linear.NoetherNormalizationKrull
public import Linear.LocalizedDifferentialRank
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.LinearAlgebra.TensorProduct.Basis
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy
universe u

/-- The actual fraction field of a characteristic-zero domain with a finite
injective polynomial normalization has differential dimension equal to the
number of normalization variables. The fraction-field tower is constructed. -/
theorem finite_normalization_fraction_differential_finrank
    {k A F : Type u} [Field k] [CharZero k] [CommRing A] [IsDomain A]
    [Algebra k A] [Field F] [Algebra A F] [Algebra k F]
    [IsScalarTower k A F] [IsFractionRing A F]
    (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hfin : g.Finite) :
    Module.finrank F (KaehlerDifferential k F) = s := by
  let R := MvPolynomial (Fin s) k
  let E := FractionRing R
  letI : Algebra R A := g.toRingHom.toAlgebra
  letI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq
    (fun a => (g.commutes a).symm)
  letI : Module.Finite R A := RingHom.finite_algebraMap.mp hfin
  let φ : R →ₐ[k] F := (IsScalarTower.toAlgHom k A F).comp g
  letI : Algebra R F := φ.toRingHom.toAlgebra
  letI : IsScalarTower k R F := IsScalarTower.of_algebraMap_eq
    (fun a => (φ.commutes a).symm)
  letI : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq' rfl
  letI : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).mpr
    ((IsFractionRing.injective A F).comp hinj)
  letI : Algebra E F := FractionRing.liftAlgebra R F
  letI : IsScalarTower R E F := FractionRing.isScalarTower_liftAlgebra R F
  letI : IsScalarTower k E F := inferInstance
  letI : Algebra.IsAlgebraic E F := isAlgebraic_of_isFractionRing R A E F
  letI : Algebra.FormallyEtale E F := Algebra.FormallyEtale.of_isSeparable E F
  letI : Algebra.FormallyEtale R E :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  letI : Algebra.FormallyEtale R F := Algebra.FormallyEtale.comp R E F
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R F
  let b := (KaehlerDifferential.mvPolynomialBasis k (Fin s)).baseChange F
  simpa using Module.finrank_eq_card_basis (b.map e)

/-- Passing to the actual fraction field and back computes the generic rank
of the actual original domain's differential module, without global smoothness. -/
theorem finite_normalization_differential_finrank
    {k A : Type u} [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hfin : g.Finite) :
    Module.finrank A (KaehlerDifferential k A) = s := by
  have hloc := localized_differential_finrank (K := k) (A := A)
    (B := FractionRing A) (nonZeroDivisors A) le_rfl
  exact hloc.symm.trans (finite_normalization_fraction_differential_finrank s g hinj hfin)

/-- The actual Krull dimension of a finite-type characteristic-zero domain
equals the rank of its actual Kähler differential module. Neither dimension
nor differential rank is a supplied formula. -/
theorem finiteType_domain_krull_dimension_eq_differential_finrank
    (k A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Module.finrank A (KaehlerDifferential k A) : WithBot ℕ∞) := by
  obtain ⟨s, g, hinj, hfin, hdim⟩ := exists_finite_normalization_krull_dimension k A
  rw [finite_normalization_differential_finrank s g hinj hfin]
  exact hdim

end LinearStudy
