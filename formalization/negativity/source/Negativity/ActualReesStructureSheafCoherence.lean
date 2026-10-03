module

public import Negativity.ActualReesFinitenessHypotheses
public import Negativity.External.Aintlib.Picard.InvertibleSheafLocallyFree

@[expose] public section

namespace Negativity
open AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The actual structure sheaf has both coherent-module properties consumed
by the imported proper-cohomology finiteness theorem. Neither property is
an additional Rees-model hypothesis. -/
theorem actual_structure_sheaf_finite_type_and_quasicoherent (W : Scheme.{u}) :
    (SheafOfModules.unit W.ringCatSheaf).IsFiniteType ∧
      (SheafOfModules.unit W.ringCatSheaf).IsQuasicoherent := by
  letI : (Scheme.Modules.unitObj W).IsFinitePresentation :=
    Scheme.Modules.isInvertible_unit.isFinitePresentation
  change (Scheme.Modules.unitObj W).IsFiniteType ∧
    (Scheme.Modules.unitObj W).IsQuasicoherent
  exact ⟨inferInstance, inferInstance⟩

end Negativity
