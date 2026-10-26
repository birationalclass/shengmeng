module
public import Linear.ProjectiveLaurentShiftCoefficients
public import Linear.ProjectiveLaurentCechShift
public import Linear.ProjectiveLaurentWeightComponents
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ] {d l : ℤ}

abbrev coordinateLaurentTupleFactor (d : ℤ) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :=
  ModuleCat.of Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (AddMonoidAlgebra Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn (fun j => (a.1 j).down)})

def coordinateLaurentTupleProjection (d : ℤ) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      coordinateLaurentTupleFactor (R := R) d a :=
  Pi.π (fun a => coordinateLaurentTupleFactor (R := R) d a) a

/-- Projection of the actual Cech shift gives actual allowed-weight multiplication. -/
theorem coordinateLaurentTupleProjection_shift {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i) :
    coordinateLaurentCechShift (R := R) (d := d) b hb n ≫
      coordinateLaurentTupleProjection (R := R) (d+l) a =
    coordinateLaurentTupleProjection (R := R) d a ≫
      ModuleCat.ofHom (homogeneousLaurentShiftLinear _ b hb) := by
  unfold coordinateLaurentTupleProjection coordinateLaurentCechShift
  exact Pi.lift_comp_π _ a

/-- An actual cochain's shifted weight component has precisely the original
coefficient on each coordinate tuple. No residue coordinates are assumed. -/
theorem coordinateLaurentCechShift_weightComponent {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i)
    (e : {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn (fun j => (a.1 j).down)})
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentWeightComponent (R := R) (d+l)
      (homogeneousLaurentAllowedShift _ b hb e).1 n
        ((coordinateLaurentCechShift (R := R) (d := d) b hb n).hom s)).1 a =
    (coordinateHomogeneousLaurentWeightComponent (R := R) d e.1 n s).1 a := by
  rw [coordinateHomogeneousLaurentWeightComponent_apply_of_allowed
      (h := (homogeneousLaurentAllowedShift _ b hb e).2),
    coordinateHomogeneousLaurentWeightComponent_apply_of_allowed (h := e.2)]
  change ((coordinateLaurentTupleProjection (R := R) (d+l) a).hom
      ((coordinateLaurentCechShift (R := R) (d := d) b hb n).hom s)).coeff
        (homogeneousLaurentAllowedShift _ b hb e) =
    ((coordinateLaurentTupleProjection (R := R) d a).hom s).coeff e
  have h := ConcreteCategory.congr_hom
    (coordinateLaurentTupleProjection_shift (R := R) (d := d) a b hb) s
  change (coordinateLaurentTupleProjection (R := R) (d+l) a).hom
    ((coordinateLaurentCechShift (R := R) (d := d) b hb n).hom s) =
    homogeneousLaurentShiftLinear _ b hb ((coordinateLaurentTupleProjection (R := R) d a).hom s) at h
  rw [h, homogeneousLaurentShiftLinear_coeff]
end MvPolynomial
