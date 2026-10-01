module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- Normal stalks imply normal coordinate rings on every nonempty affine
open. The actual scheme stalks, not abstract chosen local rings, provide
all maximal localizations used by the algebraic local criterion. -/
theorem normal_affine_sections (Y : Scheme) [IsIntegral Y]
    (hnormal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(Y, U) := by
  let R : Type _ := Γ(Y, U)
  let stalk (P : Ideal R) [P.IsMaximal] : Type _ :=
    Y.presheaf.stalk (hU.fromSpec ⟨P, inferInstance⟩)
  exact @IsIntegrallyClosed.of_isLocalization_maximal R inferInstance stalk
    (fun P _ ↦ inferInstance)
    (fun P _ ↦ Y.presheaf.algebra_section_stalk
      ⟨hU.fromSpec ⟨P, inferInstance⟩, (hU.isoSpec.inv _).2⟩)
    (fun P _ ↦ hU.isLocalization_stalk' ⟨P, inferInstance⟩ (hU.isoSpec.inv _).2)
    inferInstance (fun P _ ↦ hnormal _)

end Negativity
