module
public import Linear.SchemeModuleHomOpenImmersionRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} (M N : X.Modules)
variable (j : Y ⟶ X) [IsOpenImmersion j]

/-- The ORIGINAL restriction of local O-linear maps is a bijection
on every open of the open-immersion domain. Surjectivity is derived
from the actual slice equivalence, not assumed as a Hom certificate. -/
theorem schemeModuleHomOpenImmersionRestrictSection_bijective (W : Y.Opens) :
    Function.Bijective (schemeModuleHomOpenImmersionRestrictSection M N j W) := by
  let T := Over.post (X := W) j.opensFunctor
  letI : T.IsEquivalence := openImmersionOverPost_isEquivalence j W
  let F := (Functor.whiskeringLeft (Over W)ᵒᵖ (Over (j ''ᵁ W))ᵒᵖ Ab).obj T.op
  constructor
  · intro f g h
    apply Subtype.ext
    apply F.map_injective
    exact congrArg Subtype.val h
  · intro g
    obtain ⟨f,hf⟩ := F.map_surjective
      (X := (Over.forget (j ''ᵁ W)).op ⋙ M.presheaf)
      (Y := (Over.forget (j ''ᵁ W)).op ⋙ N.presheaf) g.val
    have hl : schemeModuleHomOverLinear M N (j ''ᵁ W) f := by
      rintro ⟨Z⟩ r x
      obtain ⟨Z',⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := T) Z
      have heq : T.obj Z' = Z :=
        CostructuredArrow.obj_ext _ _
          (le_antisymm (leOfHom e.hom.left) (leOfHom e.inv.left))
          (Subsingleton.elim _ _)
      cases heq
      have hp : f.app (op (T.obj Z')) = g.val.app (op Z') :=
        congrArg (fun t => t.app (op Z')) hf
      let r0 : Γ(X,j ''ᵁ Z'.left) := r
      let x0 : Γ(M,j ''ᵁ Z'.left) := x
      have h := g.property (op Z') ((j.appIso Z'.left).hom r0)
        (show Γ(M.restrict j,Z'.left) from x0)
      change g.val.app (op Z')
          ((j.appIso Z'.left).inv ((j.appIso Z'.left).hom r0) • x0) =
        (j.appIso Z'.left).inv ((j.appIso Z'.left).hom r0) •
          (show Γ(N,j ''ᵁ Z'.left) from g.val.app (op Z') x0) at h
      have hr : (j.appIso Z'.left).inv ((j.appIso Z'.left).hom r0) = r0 :=
        congrArg (fun q : Γ(X,j ''ᵁ Z'.left) ⟶ Γ(X,j ''ᵁ Z'.left) => q r0) (j.appIso Z'.left).hom_inv_id
      change f.app (op (T.obj Z')) (r0 • x0) =
        r0 • (show Γ(N,j ''ᵁ Z'.left) from f.app (op (T.obj Z')) x0)
      rw [hp]
      rw [hr] at h
      exact h
    refine ⟨⟨f,hl⟩,?_⟩
    apply Subtype.ext
    exact hf
end LinearStudy
