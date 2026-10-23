module
public import Linear.OrderedCrossSpaceCechCoefficientNaturality
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Compose TWO proved original coefficient squares using EXACT equalities
for the old comparisons. Keeping the object structures abstract prevents
repeated expansion of large actual-cohomology group presentations. -/
theorem originalComparisonIsoCoefficientSquare_of_factorizations
    {C : Type u} [Category.{v} C] {A A' B B' D D' : C}
    (e : A ≅ B) (e' : A' ≅ B') (j : B ≅ D) (j' : B' ≅ D')
    (old : A ≅ D) (old' : A' ≅ D') (hold : old = e ≪≫ j) (hold' : old' = e' ≪≫ j')
    (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D')
    (h1 : a ≫ e'.hom = e.hom ≫ b) (h2 : b ≫ j'.hom = j.hom ≫ d) :
    a ≫ old'.hom = old.hom ≫ d := by
  rw [hold,hold']
  exact ((show CommSq a e.hom e'.hom b from ⟨h1⟩).vert_comp
    (show CommSq b j.hom j'.hom d from ⟨h2⟩)).w
end LinearStudy
