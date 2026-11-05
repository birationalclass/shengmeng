module
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    {I J : Type} [Finite I] [Finite J]

/-- Componentwise proved naturality gives the corresponding ACTUAL
finite biproduct matrix square, with arbitrary source and target families. -/
theorem biproductMatrixComponentNaturality {a a' : I → C} {b b' : J → C}
    (u : ∀ i j, a i ⟶ b j) (v : ∀ i j, a' i ⟶ b' j)
    (ea : ∀ i, a i ⟶ a' i) (eb : ∀ j, b j ⟶ b' j)
    (h : ∀ i j, u i j ≫ eb j = ea i ≫ v i j) :
    biproduct.matrix u ≫ biproduct.map eb = biproduct.map ea ≫ biproduct.matrix v := by
  rw [biproduct.matrix_map, biproduct.map_matrix]
  congr 1
  funext i j
  exact h i j

/-- Reuse mathlib's actual biproduct preservation of additive functors.
This identifies the image of an assembled matrix with the matrix of
the original mapped entries; it is not a new abstract matrix definition. -/
theorem additiveFunctorBiproductMatrixNaturality (F : C ⥤ D) [F.Additive]
    {a : I → C} {b : J → C} (u : ∀ i j, a i ⟶ b j) :
    F.map (biproduct.matrix u) ≫ (F.mapBiproduct b).hom =
      (F.mapBiproduct a).hom ≫ biproduct.matrix (fun i j => F.map (u i j)) := by
  apply biproduct.hom_ext
  intro j
  erw [Category.assoc, Functor.mapBiproduct_hom, biproduct.lift_π]
  conv_rhs => erw [Category.assoc, biproduct.matrix_π]
  rw [← F.map_comp, biproduct.matrix_π]
  exact (biproduct.mapBiproduct_hom_desc F a (fun i => u i j)).symm

end LinearStudy
