module
public import Linear.PolynomialMapFibersFinite
public import Linear.ProjectiveConeFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Every actual affine vector fiber of the original no-base-point
homogeneous tuple is finite. -/
theorem HomogeneousEndomorphism.evalVector_fibers_finite
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) (w : CoordinateVector n) :
    (f.evalVector ⁻¹' {w}).Finite := by
  exact polynomialMap_fibers_finite f.forms (f.polynomial_map_finite hq) w

/-- Every whole projective point fiber is finite, including points outside
the previously chosen affine chart. This does not compute its degree or size. -/
theorem HomogeneousEndomorphism.onPoints_fibers_finite
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) (y : ProjectivePoint n) :
    (f.onPoints ⁻¹' {y}).Finite := by
  classical
  induction y using Projectivization.ind with
  | h w hw =>
    let m : CoordinateVector n → ProjectivePoint n := fun v =>
      if hv : v = 0 then Projectivization.mk ℂ w hw else Projectivization.mk ℂ v hv
    have hC := f.evalVector_fibers_finite hq w
    apply (hC.image m).subset
    intro z hz
    induction z using Projectivization.ind with
    | h v hv =>
      have hp : f.onPoints (Projectivization.mk ℂ v hv) = Projectivization.mk ℂ w hw := hz
      rw [f.onPoints_mk] at hp
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hp.symm
      obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) hq
      have hfw : f.evalVector (b • v) = w := by
        rw [f.evalVector_smul, hb]
        exact ha
      have hv' : b • v ≠ 0 := by
        intro h0
        rw [h0, f.evalVector_zero (Nat.ne_of_gt hq)] at hfw
        exact hw hfw.symm
      refine ⟨b • v, hfw, ?_⟩
      dsimp only [m]
      rw [dite_eq_right hv']
      exact (Projectivization.mk_eq_mk_iff' ℂ _ _ hv' hv).mpr ⟨b, rfl⟩

end LinearStudy
