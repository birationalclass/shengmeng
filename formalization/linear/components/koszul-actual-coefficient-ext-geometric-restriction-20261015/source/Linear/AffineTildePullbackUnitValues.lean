module
public import Linear.AffineTildePullbackUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- On ACTUAL original global sections, the geometric unit followed by the
SAME constructed affine comparison is the ORIGINAL scalar-extension unit. -/
theorem affineTildePullbackUnit_globalValue {R S : CommRingCat.{u}} (phi : R ⟶ S)
    (N : ModuleCat.{u} R) (n : N) :
    (tildePushforwardGlobalIso phi ((ModuleCat.extendScalars phi.hom).obj N)).hom
      (((moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi)).unit.app (tilde N) ≫
          (Scheme.Modules.pushforward (Spec.map phi)).map
            ((affineTildePullbackExtendScalarsNatIso phi).app N).hom))
        ((tilde.adjunction (R := R)).unit.app N n)) =
    (ModuleCat.extendRestrictScalarsAdj phi.hom).unit.app N n := by
  have h := congrArg (fun f => f.hom n) (affineTildePullbackUnit_square phi N)
  change (affinePushforwardGlobalSectionsNatIso phi).hom.app
      (tilde ((ModuleCat.extendScalars phi.hom).obj N))
      (((moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi)).unit.app (tilde N) ≫
          (Scheme.Modules.pushforward (Spec.map phi)).map
            ((affineTildePullbackExtendScalarsNatIso phi).app N).hom))
        ((tilde.adjunction (R := R)).unit.app N n)) =
    (tilde.isoTop ((ModuleCat.extendScalars phi.hom).obj N)).hom
      ((ModuleCat.extendRestrictScalarsAdj phi.hom).unit.app N n) at h
  change (tilde.isoTop ((ModuleCat.extendScalars phi.hom).obj N)).inv
    ((affinePushforwardGlobalSectionsNatIso phi).hom.app
      (tilde ((ModuleCat.extendScalars phi.hom).obj N))
      (((moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi)).unit.app (tilde N) ≫
          (Scheme.Modules.pushforward (Spec.map phi)).map
            ((affineTildePullbackExtendScalarsNatIso phi).app N).hom))
        ((tilde.adjunction (R := R)).unit.app N n))) = _
  exact (congrArg (tilde.isoTop ((ModuleCat.extendScalars phi.hom).obj N)).inv h).trans
    (Iso.hom_inv_id_apply _ _)

/-- The ACTUAL native affine-pushforward/global-section identification
preserves ORIGINAL coefficient maps, on original section VALUES. -/
theorem tildePushforwardGlobalIso_naturality_value {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (M N : ModuleCat.{u} S) (f : M ⟶ N)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward (Spec.map phi)).obj (tilde M))) :
    (tildePushforwardGlobalIso phi N).hom
      ((moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pushforward (Spec.map phi)).map ((tilde.functor S).map f)) x) =
    f ((tildePushforwardGlobalIso phi M).hom x) := by
  have he := congrArg (fun g => g.hom x)
    ((affinePushforwardGlobalSectionsNatIso phi).hom.naturality ((tilde.functor S).map f))
  change (affinePushforwardGlobalSectionsNatIso phi).hom.app (tilde N)
      ((moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pushforward (Spec.map phi)).map ((tilde.functor S).map f)) x) =
    (moduleSpecΓFunctor (R := S)).map ((tilde.functor S).map f)
      ((affinePushforwardGlobalSectionsNatIso phi).hom.app (tilde M) x) at he
  have ht := congrArg (fun g => g.hom
      ((affinePushforwardGlobalSectionsNatIso phi).hom.app (tilde M) x))
    ((tilde.toTildeΓNatIso (R := S)).inv.naturality f)
  change (tilde.isoTop N).inv
      ((moduleSpecΓFunctor (R := S)).map ((tilde.functor S).map f)
        ((affinePushforwardGlobalSectionsNatIso phi).hom.app (tilde M) x)) =
    f ((tilde.isoTop M).inv
      ((affinePushforwardGlobalSectionsNatIso phi).hom.app (tilde M) x)) at ht
  change (tilde.isoTop N).inv
      ((affinePushforwardGlobalSectionsNatIso phi).hom.app (tilde N)
        ((moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pushforward (Spec.map phi)).map ((tilde.functor S).map f)) x)) = _
  exact (congrArg (tilde.isoTop N).inv he).trans ht

end LinearStudy
