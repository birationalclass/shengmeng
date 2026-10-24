module
public import Linear.DiscreteSheafFlasque
public import Mathlib.Algebra.Category.Ring.Constructions
public import Linear.SchemeModuleActualCohomologyGroup
public import Linear.OriginalGlobalModuleScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- On the ACTUAL original discrete scheme, glue one on an open and zero
on its actual complement. The resulting global structure section is
idempotent. No selector, idempotent or projector is assumed as input. -/
theorem discreteScheme_exists_open_idempotent
    (D : Scheme.{u}) [DiscreteTopology D] (U : D.Opens) :
    ∃ e : Γ(D,⊤),D.presheaf.map U.leTop.op e=1 ∧
      D.presheaf.map (show D.Opens from ⟨(U : Set D)ᶜ,isOpen_discrete _⟩).leTop.op e=0 ∧
      e*e=e := by
  classical
  let W : D.Opens := ⟨(U : Set D)ᶜ,isOpen_discrete _⟩
  let F := D.sheaf
  have hUW : U ⊓ W = ⊥ := by ext x;simp [W]
  have hWU : W ⊓ U = ⊥ := by rw [inf_comm,hUW]
  letI := CommRingCat.subsingleton_of_isTerminal (F.isTerminalOfEqEmpty hUW)
  letI := CommRingCat.subsingleton_of_isTerminal (F.isTerminalOfEqEmpty hWU)
  let cover : Fin 2 → D.Opens := ![U,W]
  let sf : (i : Fin 2) → F.obj.obj (op (cover i))
    | 0 => 1
    | 1 => 0
  have hcomp : TopCat.Presheaf.IsCompatible F.obj cover sf := by
    simp only [TopCat.Presheaf.IsCompatible,Fin.forall_fin_two]
    refine ⟨⟨rfl,?_⟩,?_,rfl⟩
    all_goals
      dsimp [cover]
      exact Subsingleton.elim _ _
  have hcover : (⊤ : D.Opens) ≤ iSup cover := by
    intro x _
    by_cases hx : x ∈ U
    · exact (le_iSup cover 0) hx
    · exact (le_iSup cover 1) hx
  obtain ⟨e,he,hunique⟩ := F.existsUnique_gluing' cover ⊤
    (fun i => homOfLE (show cover i ≤ ⊤ from le_top)) hcover sf hcomp
  have heU : D.presheaf.map U.leTop.op e=1 := by
    have h := he 0
    change D.presheaf.map U.leTop.op e=1 at h
    exact h
  have heW : D.presheaf.map W.leTop.op e=0 := by
    have h := he 1
    change D.presheaf.map W.leTop.op e=0 at h
    exact h
  refine ⟨e,heU,heW,?_⟩
  apply hunique (e*e)
  intro i
  fin_cases i
  · change D.presheaf.map U.leTop.op (e*e)=1
    rw [map_mul,heU,one_mul]
  · change D.presheaf.map W.leTop.op (e*e)=0
    rw [map_mul,heW,zero_mul]
/-- The constructed original open idempotent. Its proof is the preceding
actual sheaf gluing theorem, not a chosen algebraic substitute. -/
def discreteSchemeOpenIdempotent (D : Scheme.{u}) [DiscreteTopology D]
    (U : D.Opens) : Γ(D,⊤) :=
  Classical.choose (discreteScheme_exists_open_idempotent D U)
theorem discreteSchemeOpenIdempotent_restrict_one
    (D : Scheme.{u}) [DiscreteTopology D] (U : D.Opens) :
    D.presheaf.map U.leTop.op (discreteSchemeOpenIdempotent D U)=1 :=
  (Classical.choose_spec (discreteScheme_exists_open_idempotent D U)).1
theorem discreteSchemeOpenIdempotent_restrict_complement_zero
    (D : Scheme.{u}) [DiscreteTopology D] (U : D.Opens) :
    D.presheaf.map (show D.Opens from ⟨(U : Set D)ᶜ,isOpen_discrete _⟩).leTop.op
      (discreteSchemeOpenIdempotent D U)=0 :=
  (Classical.choose_spec (discreteScheme_exists_open_idempotent D U)).2.1
theorem discreteSchemeOpenIdempotent_idempotent
    (D : Scheme.{u}) [DiscreteTopology D] (U : D.Opens) :
    discreteSchemeOpenIdempotent D U * discreteSchemeOpenIdempotent D U =
      discreteSchemeOpenIdempotent D U :=
  (Classical.choose_spec (discreteScheme_exists_open_idempotent D U)).2.2
end LinearStudy
