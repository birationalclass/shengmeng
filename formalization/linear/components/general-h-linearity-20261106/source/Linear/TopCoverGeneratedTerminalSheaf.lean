module
public import Linear.CoverGeneratedTerminalPresheaf
public import Linear.TopOpenFreeAbelianSheaf
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Adjunction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- An actual open cover makes its generated terminal subpresheaf locally surjective onto
that SAME terminal presheaf. The witness is the actual intersection with a cover member. -/
theorem topCoverGeneratedTerminal_locallySurjective (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) (hU : (⊤ : Opens X) ≤ iSup U) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Subfunctor.ofObjects.{u} U).ι := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro V s x hx
  have hxU : x ∈ iSup U := hU trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxU
  refine ⟨V ⊓ U i,inf_le_left,?_,⟨hx,hi⟩⟩
  refine ⟨⟨PUnit.unit,⟨i,⟨homOfLE inf_le_right⟩⟩⟩,?_⟩
  change (PUnit.unit : PUnit.{u+1}) = _
  exact Subsingleton.elim _ _

/-- The actual generated terminal inclusion is objectwise injective,hence locally injective. -/
theorem topCoverGeneratedTerminal_locallyInjective (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Subfunctor.ofObjects.{u} U).ι :=
  Presheaf.isLocallyInjective_of_injective _ _ (fun _ => Subtype.val_injective)

/-- After ACTUAL sheafification,the cover-generated target is isomorphic via the SAME
inclusion to the terminal sheaf. This does not yet assert the Cech/native-H comparison. -/
theorem topCoverGeneratedTerminal_sheafify_inclusion_isIso (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) (hU : (⊤ : Opens X) ≤ iSup U) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map
      (Subfunctor.ofObjects.{u} U).ι) := by
  letI := topCoverGeneratedTerminal_locallySurjective X U hU
  letI := topCoverGeneratedTerminal_locallyInjective X U
  exact ((Opens.grothendieckTopology X).W_iff _).mp
    ((Opens.grothendieckTopology X).W_of_isLocallyBijective _)
/-- Applying the ACTUAL free-abelian presheaf functor and then sheafifying retains
this target isomorphism. This is the target needed by the Cech free-sheaf augmentation. -/
theorem topCoverGeneratedTerminal_freeAbelian_sheafify_inclusion_isIso (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) (hU : (⊤ : Opens X) ≤ iSup U) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (((Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
        AddCommGrpCat.free).map (Subfunctor.ofObjects.{u} U).ι)) := by
  apply ((Opens.grothendieckTopology X).W_iff _).mp
  letI : (Opens.grothendieckTopology X).PreservesSheafification AddCommGrpCat.free :=
    Sheaf.preservesSheafification_of_adjunction (Opens.grothendieckTopology X) AddCommGrpCat.adj
  apply (Opens.grothendieckTopology X).W_of_preservesSheafification AddCommGrpCat.free
  exact ((Opens.grothendieckTopology X).W_iff _).mpr
    (topCoverGeneratedTerminal_sheafify_inclusion_isIso X U hU)
end LinearStudy