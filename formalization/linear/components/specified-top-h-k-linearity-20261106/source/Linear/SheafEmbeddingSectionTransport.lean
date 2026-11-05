module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X Z : Scheme.{u}} {M N G : X.Modules}

/-- An actual module-sheaf monomorphism is injective on every open's
sections. This statement does not assert injectivity on residue fibres. -/
theorem moduleSheafMono_sections_injective (j : M ⟶ N) [Mono j]
    (U : X.Opens) : Function.Injective (j.app U) := by
  letI : Mono j.val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules X).map j))
  exact PresheafOfModules.injective_of_mono j.val (op U)

/-- The same fixed embedding neither kills nor creates a zero section. -/
theorem moduleSheafMono_section_eq_zero_iff (j : M ⟶ N) [Mono j]
    (U : X.Opens) (s : Γ(M, U)) : j.app U s = 0 ↔ s = 0 := by
  constructor
  · intro hs
    apply moduleSheafMono_sections_injective j U
    simpa only [map_zero] using hs
  · rintro rfl
    exact (j.app U).hom.map_zero

/-- In particular the nonzero global section used in Lemma4.2 stays
nonzero after the fixed embedding from Lemma4.1. -/
theorem moduleSheafMono_section_ne_zero_iff (j : M ⟶ N) [Mono j]
    (U : X.Opens) (s : Γ(M, U)) : j.app U s ≠ 0 ↔ s ≠ 0 :=
  not_congr (moduleSheafMono_section_eq_zero_iff j U s)

/-- A module morphism commutes with the actual open restriction. -/
theorem moduleSheafMap_restriction_apply (j : M ⟶ N)
    {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (j.app U s) =
      j.app W (M.presheaf.map (homOfLE h).op s) := by
  exact (ConcreteCategory.congr_hom
    (j.mapPresheaf.naturality (homOfLE h).op) s).symm

/-- Vanishing on an open is equivalent under a sheaf embedding.
For a closed fibre only forward vanishing is valid in general; see
moduleSheafMap_pullback_vanishing below. -/
theorem moduleSheafMono_restriction_eq_zero_iff (j : M ⟶ N) [Mono j]
    {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (j.app U s) = 0 ↔
      M.presheaf.map (homOfLE h).op s = 0 := by
  rw [moduleSheafMap_restriction_apply]
  exact moduleSheafMono_section_eq_zero_iff j W _

/-- Postcomposition with the fixed embedding preserves a nonzero
section represented by its map from the structure module. -/
theorem moduleSheafMono_postcompose_ne_zero (j : M ⟶ N) [Mono j]
    (s : G ⟶ M) (hs : s ≠ 0) : s ≫ j ≠ 0 := by
  intro h
  apply hs
  apply (cancel_mono j).mp
  simpa only [zero_comp] using h

/-- Pulling back to any actual subscheme, including a closed point or
closed fibre, preserves vanishing of a section after any module map.
No false assertion that pullback preserves monomorphisms is made. -/
theorem moduleSheafMap_pullback_vanishing (i : Z ⟶ X) (j : M ⟶ N)
    (s : G ⟶ M) (hs : (Scheme.Modules.pullback i).map s = 0) :
    (Scheme.Modules.pullback i).map (s ≫ j) = 0 := by
  rw [Functor.map_comp, hs, zero_comp]
end LinearStudy
