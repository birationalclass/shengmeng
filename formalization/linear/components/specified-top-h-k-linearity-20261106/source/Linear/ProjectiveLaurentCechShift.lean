module
public import Linear.ProjectiveLaurentShiftLinear
public import Linear.ProjectiveLaurentCechWeights
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ] {d l : ℤ}

def coordinateLaurentCechShift (b : HomogeneousLaurentExponent σ l)
    (hb : ∀ i, 0 ≤ b.1 i) (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) (d+l) n :=
  Pi.lift fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    Pi.π (fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      ModuleCat.of Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn (fun j => (a.1 j).down)})) a ≫
    ModuleCat.ofHom (homogeneousLaurentShiftLinear (fun j => (a.1 j).down) b hb)

theorem coordinateLaurentCechShift_coface (b : HomogeneousLaurentExponent σ l)
    (hb : ∀ i, 0 ≤ b.1 i) (n : ℕ) (k : Fin (n+2)) :
    coordinateLaurentCechShift (R := R) (d := d) b hb n ≫
      coordinateHomogeneousLaurentOrderedCechCoface (R := R) (d+l) n k =
    coordinateHomogeneousLaurentOrderedCechCoface (R := R) d n k ≫
      coordinateLaurentCechShift (R := R) b hb (n+1) := by
  unfold coordinateLaurentCechShift coordinateHomogeneousLaurentOrderedCechCoface
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_comp_π, ← Category.assoc, Pi.lift_comp_π]
  conv_rhs => erw [Category.assoc, Pi.lift_comp_π, ← Category.assoc, Pi.lift_comp_π]
  rw [Category.assoc, Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  exact homogeneousLaurentShiftLinear_delete a k b hb

theorem coordinateLaurentCechShift_differential (b : HomogeneousLaurentExponent σ l)
    (hb : ∀ i, 0 ≤ b.1 i) (n : ℕ) :
    coordinateLaurentCechShift (R := R) (d := d) b hb n ≫
      coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (d+l) n =
    coordinateHomogeneousLaurentOrderedCechDifferential (R := R) d n ≫
      coordinateLaurentCechShift (R := R) b hb (n+1) := by
  rw [coordinateHomogeneousLaurentOrderedCechDifferential,
    coordinateHomogeneousLaurentOrderedCechDifferential,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, coordinateLaurentCechShift_coface]
end MvPolynomial
