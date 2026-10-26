module
public import Linear.AffineTildePullbackUnitValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TensorProduct
open scoped ChangeOfRings
universe u
attribute [local irreducible] affineTildePullbackExtendScalarsNatIso
  tildePushforwardGlobalIso extendScalarsActualTensorLinearEquiv

/-- ORIGINAL geometric unit sends an ORIGINAL coefficient n to 1 tensor n
under the SAME actual affine geometric-pullback/native-tensor iso. Any
original N is allowed; no FP/flat/free/invertibility/CM or value premise. -/
theorem affineTildeTensorPullbackUnit_globalValue (R S : CommRingCat.{u})
    [Algebra R S] (N : ModuleCat.{u} R) (n : N) :
    (tildePushforwardGlobalIso (CommRingCat.ofHom (algebraMap R S))
      (ModuleCat.of S (S ⊗[R] N))).hom
      (((moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).unit.app (tilde N) ≫
          (Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
            (affineTildeTensorPullbackIso R S N).hom))
        ((tilde.adjunction (R := R)).unit.app N n)) = (1 : S) ⊗ₜ[R] n := by
  let x := ((moduleSpecΓFunctor (R := R)).map
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).unit.app (tilde N) ≫
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((affineTildePullbackExtendScalarsNatIso
          (CommRingCat.ofHom (algebraMap R S))).app N).hom))
      ((tilde.adjunction (R := R)).unit.app N n)
  have hx := affineTildePullbackUnit_globalValue
    (CommRingCat.ofHom (algebraMap R S)) N n
  have hn := tildePushforwardGlobalIso_naturality_value
    (CommRingCat.ofHom (algebraMap R S))
    ((ModuleCat.extendScalars (algebraMap R S)).obj N)
    (ModuleCat.of S (S ⊗[R] N))
    (extendScalarsActualTensorLinearEquiv (S := S) N).toModuleIso.hom x
  have hc : ((moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).unit.app (tilde N) ≫
        (Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
          (affineTildeTensorPullbackIso R S N).hom))
      ((tilde.adjunction (R := R)).unit.app N n) =
    (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((tilde.functor S).map
          (extendScalarsActualTensorLinearEquiv (S := S) N).toModuleIso.hom)) x := by
    simp only [x, affineTildeTensorPullbackIso, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, ModuleCat.comp_apply]
    rfl
  refine (congrArg (tildePushforwardGlobalIso
    (CommRingCat.ofHom (algebraMap R S)) (ModuleCat.of S (S ⊗[R] N))).hom hc).trans ?_
  refine hn.trans ?_
  change extendScalarsActualTensorLinearEquiv (S := S) N
    ((tildePushforwardGlobalIso (CommRingCat.ofHom (algebraMap R S))
      ((ModuleCat.extendScalars (algebraMap R S)).obj N)).hom x) = _
  exact (congrArg (extendScalarsActualTensorLinearEquiv (S := S) N) hx).trans
    (extendScalarsActualTensorLinearEquiv_tmul N (1 : S) n)

end LinearStudy
