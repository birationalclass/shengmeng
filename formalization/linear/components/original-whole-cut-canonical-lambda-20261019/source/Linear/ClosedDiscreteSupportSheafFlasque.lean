module
public import Linear.DiscreteSheafFlasque
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Extend original sections by zero away from S intersect the smaller open. Every open slice of S is closed, and actual sections off S vanish. No flasqueness or cohomology vanishing is assumed. -/
theorem closedDiscreteSupportAbelianSheaf_restriction_surjective
    {X : TopCat.{u}} (S : Set X)
    (hclosed : ∀ V : Opens X, IsClosed (S ∩ (V : Set X)))
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hzero : ∀ T : Opens X, Disjoint (T : Set X) S → Subsingleton (F.obj.obj (op T)))
    {U V : Opens X} (i : V ⟶ U) : Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  let W : Opens X := ⟨(U : Set X) \ (S ∩ (V : Set X)),U.isOpen.sdiff (hclosed V)⟩
  have hVW : Disjoint ((V ⊓ W : Opens X) : Set X) S := by
    rw [Set.disjoint_left]
    intro x hx hxS
    exact hx.2.2 ⟨hxS,hx.1⟩
  have hWV : Disjoint ((W ⊓ V : Opens X) : Set X) S := by simpa only [inf_comm] using hVW
  letI := hzero (V ⊓ W) hVW
  letI := hzero (W ⊓ V) hWV
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
    · exact (le_iSup f 1) ⟨hx,fun h => hxV h.2⟩
  obtain ⟨t,ht,_⟩ := F.existsUnique_gluing' f U
    (fun j => homOfLE (hle j)) hcover sf hcomp
  refine ⟨t,?_⟩
  have ht0 := ht 0
  dsimp [f,sf] at ht0
  rw [Subsingleton.elim (homOfLE (hle 0) : V ⟶ U) i] at ht0
  exact ht0
/-- Actual abelian sheaves supported on a closed discrete subset are flasque, with their SAME original restriction maps. -/
theorem closedDiscreteSupportAbelianSheaf_isFlasque
    {X : TopCat.{u}} (S : Set X)
    (hclosed : ∀ V : Opens X, IsClosed (S ∩ (V : Set X)))
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hzero : ∀ T : Opens X, Disjoint (T : Set X) S → Subsingleton (F.obj.obj (op T))) :
    TopCat.Sheaf.IsFlasque F where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (closedDiscreteSupportAbelianSheaf_restriction_surjective S hclosed F hzero i.unop)
end LinearStudy
