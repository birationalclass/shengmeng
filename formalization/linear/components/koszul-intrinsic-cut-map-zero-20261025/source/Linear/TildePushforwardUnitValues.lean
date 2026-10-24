module
public import Linear.AffineTildePullbackUnitValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
attribute [local irreducible] tildePushforwardGlobalIso

/-- The SAME constructed affine tilde-pushforward iso retains ORIGINAL
coefficient values under the ACTUAL original global-section iso. -/
theorem tildePushforwardIso_globalValue {R S : CommRingCat.{u}} (phi : R ⟶ S)
    (M : ModuleCat.{u} S) (m : M) :
    (tildePushforwardGlobalIso phi M).hom
      ((moduleSpecΓFunctor (R := R)).map (tildePushforwardIso phi M).hom
        ((tilde.adjunction (R := R)).unit.app
          ((ModuleCat.restrictScalars phi.hom).obj M) m)) = m := by
  let P := (Scheme.Modules.pushforward (Spec.map phi)).obj (tilde M)
  let e := tildePushforwardGlobalIso phi M
  have hn := congrArg (fun f => f.hom m)
    ((tilde.adjunction (R := R)).unit.naturality e.inv)
  change (tilde.adjunction (R := R)).unit.app (moduleSpecΓFunctor.obj P) (e.inv m) =
    (moduleSpecΓFunctor (R := R)).map ((tilde.functor R).map e.inv)
      ((tilde.adjunction (R := R)).unit.app
        ((ModuleCat.restrictScalars phi.hom).obj M) m) at hn
  have ht := congrArg (fun f => f.hom (e.inv m))
    ((tilde.adjunction (R := R)).right_triangle_components P)
  change (moduleSpecΓFunctor (R := R)).map P.fromTildeΓ
    ((tilde.adjunction (R := R)).unit.app (moduleSpecΓFunctor.obj P) (e.inv m)) = e.inv m at ht
  have hv : (moduleSpecΓFunctor (R := R)).map (tildePushforwardIso phi M).hom
      ((tilde.adjunction (R := R)).unit.app
        ((ModuleCat.restrictScalars phi.hom).obj M) m) = e.inv m := by
    simp only [tildePushforwardIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, asIso_hom, Functor.map_comp, ModuleCat.comp_apply]
    exact (congrArg ((moduleSpecΓFunctor (R := R)).map P.fromTildeΓ) hn.symm).trans ht
  exact (congrArg e.hom hv).trans (Iso.inv_hom_id_apply e m)

end LinearStudy
