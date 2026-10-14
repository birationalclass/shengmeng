module
public import Linear.AffineTildeTensorPullbackUnit
public import Linear.TildeCoefficientQuotientUnitValues
public import Linear.TildeCoefficientQuotientGeometricPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TensorProduct
universe u
attribute [local irreducible] affineTildeTensorPullbackIso
  affineTildePullbackExtendScalarsNatIso tildePushforwardGlobalIso
  tildeCoefficientQuotientPushforwardIso

/-- The SAME ORIGINAL coefficient quotient morphism is the ACTUAL original
geometric restriction unit on SAME closed cut. The geometric UNIT diagram
is proved; arbitrary original N has no FP/flat/free/invertibility/CM premise. -/
theorem tildeCoefficientQuotientGeometricPullbackPushforwardIso_unit
    (R : CommRingCat.{u}) (J : Ideal R) (N : ModuleCat.{u} R) :
    (tilde.functor R).map (ModuleCat.ofHom (J • (⊤ : Submodule R N)).mkQ) ≫
      (tildeCoefficientQuotientGeometricPullbackPushforwardIso R J N).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).unit.app (tilde N) := by
  let phi : R ⟶ CommRingCat.of (R ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let T := ModuleCat.of (R ⧸ J) ((R ⧸ J) ⊗[R] N)
  let Q := ModuleCat.of R (N ⧸ (J • (⊤ : Submodule R N)))
  let P := (Scheme.Modules.pushforward (Spec.map phi)).obj (tilde T)
  apply (cancel_mono ((Scheme.Modules.pushforward (Spec.map phi)).map
    (affineTildeTensorPullbackIso R (CommRingCat.of (R ⧸ J)) N).hom)).mp
  simp only [phi, tildeCoefficientQuotientGeometricPullbackPushforwardIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_map, Category.comp_id]
  apply ((tilde.adjunction (R := R)).homEquiv N P).injective
  simp only [Adjunction.homEquiv_unit]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro n
  apply (tildePushforwardGlobalIso phi T).toLinearEquiv.injective
  change (tildePushforwardGlobalIso phi T).hom
      (((moduleSpecΓFunctor (R := R)).map
        ((tilde.functor R).map (ModuleCat.ofHom (J • (⊤ : Submodule R N)).mkQ) ≫
          (tildeCoefficientQuotientPushforwardIso R J N).hom))
        ((tilde.adjunction (R := R)).unit.app N n)) =
    (tildePushforwardGlobalIso phi T).hom
      (((moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi)).unit.app (tilde N) ≫
          (Scheme.Modules.pushforward (Spec.map phi)).map
            (affineTildeTensorPullbackIso R (CommRingCat.of (R ⧸ J)) N).hom))
        ((tilde.adjunction (R := R)).unit.app N n))
  have hu := congrArg (fun f => f.hom n)
    ((tilde.adjunction (R := R)).unit.naturality
      (ModuleCat.ofHom (J • (⊤ : Submodule R N)).mkQ))
  change (tilde.adjunction (R := R)).unit.app Q (Submodule.Quotient.mk n) =
    (moduleSpecΓFunctor (R := R)).map
      ((tilde.functor R).map (ModuleCat.ofHom (J • (⊤ : Submodule R N)).mkQ))
      ((tilde.adjunction (R := R)).unit.app N n) at hu
  have hq := tildeCoefficientQuotientPushforwardIso_globalValue R J N n
  have ht := affineTildeTensorPullbackUnit_globalValue R (CommRingCat.of (R ⧸ J)) N n
  simp only [Functor.map_comp, ModuleCat.comp_apply]
  exact (congrArg (fun x => (tildePushforwardGlobalIso phi T).hom
    ((moduleSpecΓFunctor (R := R)).map
      (tildeCoefficientQuotientPushforwardIso R J N).hom x)) hu.symm).trans
      (hq.trans ht.symm)

end LinearStudy
