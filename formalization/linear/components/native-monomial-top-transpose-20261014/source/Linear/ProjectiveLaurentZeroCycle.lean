module
public import Linear.OrderedCechSupportZero
public import Linear.ProjectiveLaurentWeightAssembly
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]

/-- A degree-zero Laurent cocycle has the same coefficient on every
coordinate chart. Coefficients at disallowed weights are already zero. -/
theorem coordinateHomogeneousLaurentZeroCycle_component_constant
    (d : ℤ) (e : HomogeneousLaurentExponent σ d) (j : σ)
    (x : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d 0)
    (hx : (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d 0).hom x = 0) :
    ∀ a, (coordinateHomogeneousLaurentWeightComponent (R := R) d e 0 x).1 a =
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e 0 x).1
        (Scheme.Modules.orderedCechSingleton (ULift.up j)) := by
  apply LinearStudy.orderedCechSupport_zeroCycle_constant
  rw [← coordinateHomogeneousLaurentWeightComponent_differential,hx,map_zero]

/-- An active weight of a global zero cocycle in nonnegative degree has
no negative exponent. This follows from actual chart compatibility, rather
than an assumed polynomial description of global sections. -/
theorem coordinateHomogeneousLaurentZeroCycle_active_nonnegative
    [Fintype σ] (d : ℤ) (hd : 0 ≤ d) (j : σ)
    (x : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d 0)
    (hx : (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d 0).hom x = 0)
    (e : HomogeneousLaurentExponent σ d)
    (he : e ∈ coordinateHomogeneousLaurentActiveWeights d 0 x) :
    ∀ i, 0 ≤ e.1 i := by
  intro i
  by_contra hi
  have hi' : e.1 i < 0 := lt_of_not_ge hi
  obtain ⟨t,ht⟩ := e.exists_not_mem_liftedNegativeSupport_of_nonneg j hd
  have hN : e.liftedNegativeSupport.Nonempty := ⟨ULift.up i,hi'⟩
  have hcycle : LinearStudy.orderedCechSupportDifferential
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.liftedNegativeSupport 0
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e 0 x) = 0 := by
    rw [← coordinateHomogeneousLaurentWeightComponent_differential,hx,map_zero]
  have hz := LinearStudy.orderedCechSupport_zeroCycle_eq_zero
    e.liftedNegativeSupport hN t ht
    (coordinateHomogeneousLaurentWeightComponent (R := R) d e 0 x) hcycle
  obtain ⟨a,ha,hcoeff⟩ := (mem_coordinateHomogeneousLaurentActiveWeights_iff d 0 x e).mp he
  have hvalue := congrArg (fun s => s.1 a) hz
  rw [coordinateHomogeneousLaurentWeightComponent_apply_of_allowed (h := ha)] at hvalue
  exact hcoeff hvalue
end MvPolynomial
