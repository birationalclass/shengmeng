module

public import Negativity.GenericNormalizationBirational
public import Negativity.FiniteNormalGeometry
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

/-- Final theorem: normalization of an actual normal integral scheme
locally of finite type over a perfect field is an actual Scheme
isomorphism. Finiteness and geometric birationality are derived, not inputs. -/
theorem finiteType_perfectField_normal_normalization_isIso
    (Y : Scheme.{u}) [IsIntegral Y] (k : Type u) [Field k] [PerfectField k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    IsIso (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  have := finiteType_perfectField_normalization_isFinite Y k b
  exact finite_normal_birational_isIso _
    (finiteType_perfectField_normalization_birational Y k b) hn

end Negativity
