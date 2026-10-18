module
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
import all Mathlib.Topology.Sheaves.Abelian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

/-- Actual additive stalk exactness follows from exactness of the SAME
section maps on all subopens of ONE actual neighborhood. Only native
germ representatives and equality after restriction are used. -/
theorem additivePresheafShortComplex_stalk_exact_of_nearby_sections
    {X : TopCat.{u}} (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{u} X))
    (x : X) (U : Opens X) (hx : x ∈ U)
    (he : ∀ W : Opens X,W ≤ U → ∀ t : S.X₂.obj (op W),
      S.g.app (op W) t = 0 → ∃ z : S.X₁.obj (op W),S.f.app (op W) z = t) :
    letI : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive :=
      TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) x
    (S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact := by
  letI : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) x
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  obtain ⟨V,hxV,s,rfl⟩ := S.X₂.exists_germ_eq y
  let Z := V ⊓ U
  have hxZ : x ∈ Z := ⟨hxV,hx⟩
  let iz : Z ⟶ V := homOfLE inf_le_left
  let t := S.X₂.map iz.op s
  have ht : S.X₂.germ Z x hxZ t = S.X₂.germ V x hxV s :=
    S.X₂.germ_res_apply iz x hxZ s
  have hz : S.X₃.germ Z x hxZ (S.g.app (op Z) t) = S.X₃.germ Z x hxZ 0 := by
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,ht]
    simpa using hy
  obtain ⟨W,hxW,iW,_,hzero⟩ := S.X₃.germ_eq x hxZ hxZ _ _ hz
  have hzW : S.g.app (op W) (S.X₂.map iW.op t) = 0 := by
    rw [← ConcreteCategory.comp_apply,S.g.naturality,ConcreteCategory.comp_apply]
    simpa using hzero
  obtain ⟨z,hz⟩ := he W (iW.le.trans inf_le_right) _ hzW
  refine ⟨S.X₁.germ W x hxW z,?_⟩
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,hz,
    S.X₂.germ_res_apply iW x hxW t,ht]

end LinearStudy