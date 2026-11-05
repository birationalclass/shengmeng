module
public import Linear.ProjectiveLaurentWeightShift
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {σ : Type} {d l : ℤ}

/-- Linear extension of actual exponent addition on allowed Laurent terms. -/
def homogeneousLaurentShiftLinear {n : ℕ} (a : Fin (n+1) → σ)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i) :
    AddMonoidAlgebra R {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn a} →ₗ[R]
    AddMonoidAlgebra R {e : HomogeneousLaurentExponent σ (d+l) // e.IsAllowedOn a} :=
  AddMonoidAlgebra.mapDomainLinearMap R R (homogeneousLaurentAllowedShift a b hb)

/-- All cofaces commute with the linearly extended exponent shift. This
does not yet identify that shift with multiplication of native sheaves. -/
theorem homogeneousLaurentShiftLinear_delete [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n+1))
    (k : Fin (n+2)) (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i) :
    (coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k (d+l)).comp
      (homogeneousLaurentShiftLinear _ b hb) =
    (homogeneousLaurentShiftLinear _ b hb).comp
      (coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d) := by
  unfold homogeneousLaurentShiftLinear coordinateHomogeneousLaurentDeleteLinearMap
  rw [← AddMonoidAlgebra.mapDomainLinearMap_comp, ← AddMonoidAlgebra.mapDomainLinearMap_comp]
  rfl
end MvPolynomial
