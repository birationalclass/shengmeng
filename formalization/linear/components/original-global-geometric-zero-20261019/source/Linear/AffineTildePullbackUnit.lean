module
public import Linear.AffineTildeTensorPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- ORIGINAL geometric unit is compatible with the SAME constructed affine
pullback comparison and ORIGINAL extension-of-scalars unit. All maps
are actual adjunction units; no map-value compatibility is an input. -/
theorem affineTildePullbackUnit_square {R S : CommRingCat.{u}} (phi : R ⟶ S)
    (N : ModuleCat.{u} R) :
    (tilde.adjunction (R := R)).unit.app N ≫
      (moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi)).unit.app (tilde N) ≫
          (Scheme.Modules.pushforward (Spec.map phi)).map
            ((affineTildePullbackExtendScalarsNatIso phi).app N).hom) ≫
      (affinePushforwardGlobalSectionsNatIso phi).hom.app
        (tilde ((ModuleCat.extendScalars phi.hom).obj N)) =
    (ModuleCat.extendRestrictScalarsAdj phi.hom).unit.app N ≫
      (ModuleCat.restrictScalars phi.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars phi.hom).obj N)) := by
  let adj1 := (((tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi))).ofNatIsoRight
      (affinePushforwardGlobalSectionsNatIso phi))
  let adj2 := ((ModuleCat.extendRestrictScalarsAdj phi.hom).comp
    (tilde.adjunction (R := S)))
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2 N
  have h' : (tilde.adjunction (R := R)).unit.app N ≫
      (moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi)).unit.app (tilde N)) ≫
      (affinePushforwardGlobalSectionsNatIso phi).hom.app
        ((Scheme.Modules.pullback (Spec.map phi)).obj (tilde N)) ≫
      (ModuleCat.restrictScalars phi.hom).map
        ((moduleSpecΓFunctor (R := S)).map
          ((affineTildePullbackExtendScalarsNatIso phi).app N).hom) =
    (ModuleCat.extendRestrictScalarsAdj phi.hom).unit.app N ≫
      (ModuleCat.restrictScalars phi.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars phi.hom).obj N)) := by
    change adj1.unit.app N ≫
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars phi.hom).map
        ((adj1.leftAdjointUniq adj2).hom.app N) = adj2.unit.app N at h
    simp only [adj1, adj2, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Adjunction.comp_unit_app, Category.assoc,
      Functor.comp_map] at h
    convert h using 1 <;> rfl
  have hn : (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pushforward (Spec.map phi)).map
        ((affineTildePullbackExtendScalarsNatIso phi).app N).hom) ≫
      (affinePushforwardGlobalSectionsNatIso phi).hom.app
        (tilde ((ModuleCat.extendScalars phi.hom).obj N)) =
    (affinePushforwardGlobalSectionsNatIso phi).hom.app
        ((Scheme.Modules.pullback (Spec.map phi)).obj (tilde N)) ≫
      (ModuleCat.restrictScalars phi.hom).map
        ((moduleSpecΓFunctor (R := S)).map
          ((affineTildePullbackExtendScalarsNatIso phi).app N).hom) :=
    (affinePushforwardGlobalSectionsNatIso phi).hom.naturality
      ((affineTildePullbackExtendScalarsNatIso phi).app N).hom
  simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (fun f => (tilde.adjunction (R := R)).unit.app N ≫
    (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi)).unit.app (tilde N)) ≫ f)
    hn).trans h'

end LinearStudy
