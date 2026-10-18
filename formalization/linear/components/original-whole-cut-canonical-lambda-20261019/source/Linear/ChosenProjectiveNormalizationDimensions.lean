module
public import Linear.ProjectiveLinearNormalization
public import Linear.IntegralKrullDimension
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- Derive the cone dimension from the SAME CHOSEN original finite
injective normalization map. No dimension conclusion is an input. -/
theorem chosenProjectiveNormalization_cone_dimension
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    ringKrullDim (CoordinateRing n ⧸ V.ideal.toIdeal) = ((r+1 : ℕ) : WithBot ℕ∞) := by
  let R := MvPolynomial (Fin (r+1)) ℂ
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  letI : Algebra R A := (projectiveLinearNormalizationMap V L).toRingHom.toAlgebra
  letI : Module.Finite R A := RingHom.finite_algebraMap.mp hfinite
  letI : Algebra.IsIntegral R A := inferInstance
  have hd := integral_injective_ringKrullDim_eq R A hinj
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field,Nat.card_fin,zero_add] at hd
  exact hd.symm

/-- The SAME chosen original normalization rank is the ACTUAL original
nonempty X0-chart dimension,using the existing cone/Hilbert/chart bridge. -/
theorem chosenProjectiveNormalization_chart_dimension
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) := by
  obtain ⟨P,hP,_,hcone,hHilbert⟩ := projective_cone_hilbertPolynomial_krull_dimension V
  have hh : P.natDegree = r := by
    have hd := hcone.symm.trans (chosenProjectiveNormalization_cone_dimension V L hinj hfinite)
    have hd' : P.natDegree+1 = r+1 := by exact_mod_cast hd
    omega
  simpa only [hh] using projective_chart_krull_dimension_of_hilbertPolynomial V x hx P hP hHilbert

/-- Original Setup r<n forces a NONZERO homogeneous defining ideal.
This discharges that explicit branch condition for the actual manuscript,
without adding a general zero-ideal theorem outside the Setup. -/
theorem chosenProjectiveNormalization_definingIdeal_ne_bot
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (hrn : r < n) :
    V.ideal.toIdeal ≠ ⊥ := by
  intro hzero
  have hd := chosenProjectiveNormalization_cone_dimension V L hinj hfinite
  rw [hzero] at hd
  have hq : ringKrullDim (CoordinateRing n ⧸ (⊥ : Ideal (CoordinateRing n))) =
      ringKrullDim (CoordinateRing n) := (RingEquiv.quotientBot (CoordinateRing n)).ringKrullDim
  have hp : ringKrullDim (CoordinateRing n) = ((n+1 : ℕ) : WithBot ℕ∞) := by
    change ringKrullDim (MvPolynomial (Fin (n+1)) ℂ) = _
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field,Nat.card_fin,zero_add]
  have hcast : ((r+1 : ℕ) : WithBot ℕ∞) = ((n+1 : ℕ) : WithBot ℕ∞) :=
    hd.symm.trans (hq.trans hp)
  have h : r+1=n+1 := by exact_mod_cast hcast
  omega

end LinearStudy
