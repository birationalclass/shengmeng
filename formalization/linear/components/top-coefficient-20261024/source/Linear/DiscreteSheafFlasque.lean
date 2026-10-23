module
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.Grp.Zero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

/-- Actual empty-open sections of an abelian sheaf are zero,using the
native sheaf terminal-object theorem;no stalk/support certificate. -/
theorem abelianSheaf_sections_subsingleton_of_eq_empty
    {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {U : Opens X} (hU : U = ⊥) : Subsingleton (F.obj.obj (op U)) :=
  AddCommGrpCat.subsingleton_of_isZero ((isZero_zero _).of_iso
    ((F.isTerminalOfEqEmpty hU).uniqueUpToIso (isZero_zero _).isTerminal))

/-- On an actual discrete space,extend a section by zero on the actual
open complement. The native sheaf gluing produces the original section
restriction preimage. No finite support or acyclicity premise. -/
theorem discreteAbelianSheaf_restriction_surjective
    {X : TopCat.{u}} [DiscreteTopology X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {U V : Opens X} (i : V ⟶ U) :
    Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  let W : Opens X := ⟨(U : Set X) \ (V : Set X),isOpen_discrete _⟩
  have hVW : V ⊓ W = ⊥ := by
    ext x
    simp [W]
  have hWV : W ⊓ V = ⊥ := by rw [inf_comm,hVW]
  letI := abelianSheaf_sections_subsingleton_of_eq_empty F hVW
  letI := abelianSheaf_sections_subsingleton_of_eq_empty F hWV
  let f : Fin 2 → Opens X := ![V,W]
  let sf : (j : Fin 2) → F.obj.obj (op (f j))
    | 0 => s
    | 1 => 0
  have hcomp : TopCat.Presheaf.IsCompatible F.obj f sf := by
    simp only [TopCat.Presheaf.IsCompatible,Fin.forall_fin_two]
    refine ⟨⟨rfl,?_⟩,?_,rfl⟩
    all_goals
      dsimp [f]
      exact Subsingleton.elim _ _
  have hle : ∀ j : Fin 2,f j ≤ U := by
    intro j
    fin_cases j
    · exact i.le
    · exact fun x hx => hx.1
  have hcover : U ≤ iSup f := by
    intro x hx
    by_cases hxV : x ∈ V
    · exact (le_iSup f 0) hxV
    · exact (le_iSup f 1) ⟨hx,hxV⟩
  obtain ⟨t,ht,_⟩ := F.existsUnique_gluing' f U
    (fun j => homOfLE (hle j)) hcover sf hcomp
  refine ⟨t,?_⟩
  have ht0 := ht 0
  dsimp [f,sf] at ht0
  rw [Subsingleton.elim (homOfLE (hle 0) : V ⟶ U) i] at ht0
  exact ht0

/-- Every actual abelian sheaf on a discrete space is flasque,with its
ORIGINAL restriction maps;derived from zero extension,not assumed. -/
theorem discreteAbelianSheaf_isFlasque
    {X : TopCat.{u}} [DiscreteTopology X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) : TopCat.Sheaf.IsFlasque F where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (discreteAbelianSheaf_restriction_surjective F i.unop)

end LinearStudy
