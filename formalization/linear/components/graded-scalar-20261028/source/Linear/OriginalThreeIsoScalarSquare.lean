module
public import Mathlib.CategoryTheory.CommSq
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Compose three proved endomorphism squares with the EXACT original
three-isomorphism comparison; no comparison square is assumed. -/
theorem originalThreeIso_endomorphism_square
    {C : Type u} [Category.{v} C] {A0 A1 B1 B0 : C}
    (eA : A1 ≅ A0) (e : A1 ≅ B1) (eB : B1 ≅ B0)
    (a0 : A0 ⟶ A0) (a1 : A1 ⟶ A1) (b1 : B1 ⟶ B1) (b0 : B0 ⟶ B0)
    (hA : CommSq a0 eA.inv eA.inv a1)
    (h : CommSq a1 e.hom e.hom b1)
    (hB : CommSq b1 eB.hom eB.hom b0) :
    (eA.symm ≪≫ e ≪≫ eB).hom ≫ b0 = a0 ≫ (eA.symm ≪≫ e ≪≫ eB).hom :=
  (hA.vert_comp (h.vert_comp hB)).w.symm
end LinearStudy
