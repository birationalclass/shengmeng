module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X : Scheme.{u}}

/-- An ACTUAL module sheaf vanishes if its ACTUAL restrictions on a
cover of original opens vanish. Reuse native uniqueness of sheaf gluing. -/
theorem schemeModule_isZero_of_over_cover (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (hM : ∀ i, IsZero (M.over (U i))) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  ext V s
  change s = (0 : Γ(M,V.unop))
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf,Scheme.Modules.isSheaf M⟩
  let W : ι → X.Opens := fun i => V.unop ⊓ U i
  have hW : V.unop ≤ iSup W := by
    dsimp only [W]
    rw [← inf_iSup_eq,hcover,inf_top_eq]
  apply F.eq_of_locally_eq' W V.unop
    (fun i => homOfLE inf_le_left) hW s 0
  intro i
  let T : Over (U i) := Over.mk (homOfLE (inf_le_right : W i ≤ U i))
  let z : (M.over (U i)).val.obj (op T) :=
    M.presheaf.map (homOfLE (inf_le_left : W i ≤ V.unop)).op s
  have he : z = 0 := congrArg
    (fun f : M.over (U i) ⟶ M.over (U i) => (f.val.app (op T)).hom z)
    ((hM i).eq_of_tgt (𝟙 _) 0)
  change M.presheaf.map (homOfLE (inf_le_left : W i ≤ V.unop)).op s =
    M.presheaf.map (homOfLE (inf_le_left : W i ≤ V.unop)).op 0
  rw [map_zero]
  exact he

end LinearStudy
