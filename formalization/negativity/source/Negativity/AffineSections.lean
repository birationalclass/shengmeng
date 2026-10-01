module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- A nonzero actual quasi-coherent sheaf on an affine Scheme has a nonzero
global section. This proves the affine section-existence step, once nonzeroness
and quasicoherence of the relevant direct image are established. -/
theorem affine_quasicoherent_exists_nonzero_section (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] (hM : ¬ IsZero M) :
    ∃ s : (moduleSpecΓFunctor.obj M), s ≠ 0 := by
  by_contra h
  have hzero : ∀ s : (moduleSpecΓFunctor.obj M), s = 0 := by
    simpa using h
  have : Subsingleton (moduleSpecΓFunctor.obj M) :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  have hz := ModuleCat.isZero_of_subsingleton (moduleSpecΓFunctor.obj M)
  have ht := (tilde.functor R).map_isZero hz
  exact hM (ht.of_iso (asIso M.fromTildeΓ).symm)

end Negativity
