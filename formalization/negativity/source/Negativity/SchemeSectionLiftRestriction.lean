module
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Tactic
@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u

/-- Final theorem: genuine section lifts restrict along actual scheme
maps. Keeping this generic avoids expanding concrete closed-image sheaves. -/
theorem actual_scheme_section_lift_restriction {X Z W F : Scheme.{u}}
    (j : W ⟶ Z) (i : Z ⟶ X) (q : F ⟶ W)
    (s : Γ(X, ⊤)) (b : Γ(Z, ⊤))
    (h : (j ≫ i).appTop s = j.appTop b) :
    (q ≫ j ≫ i).appTop s = (q ≫ j).appTop b := by
  have hh := congrArg q.appTop h
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hh

end Negativity
