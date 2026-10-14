module
public import Linear.TildePushforwardUnitValues
public import Linear.TildeCoefficientQuotientPushforward
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TensorProduct
universe u
attribute [local irreducible] tildePushforwardGlobalIso tildePushforwardIso

/-- SAME ORIGINAL coefficient quotient restriction n mod JN corresponds
to 1 tensor n under SAME constructed actual closed-cut pushforward iso.
The value compatibility is PROVED, not supplied as a condition. -/
theorem tildeCoefficientQuotientPushforwardIso_globalValue
    (R : CommRingCat.{u}) (J : Ideal R) (N : ModuleCat.{u} R) (n : N) :
    (tildePushforwardGlobalIso (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (ModuleCat.of (R ⧸ J) ((R ⧸ J) ⊗[R] N))).hom
      ((moduleSpecΓFunctor (R := R)).map
        (tildeCoefficientQuotientPushforwardIso R J N).hom
        ((tilde.adjunction (R := R)).unit.app
          (ModuleCat.of R (N ⧸ (J • (⊤ : Submodule R N)))) (Submodule.Quotient.mk n))) =
    (1 : R ⧸ J) ⊗ₜ[R] n := by
  let phi : R ⟶ CommRingCat.of (R ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let T := ModuleCat.of (R ⧸ J) ((R ⧸ J) ⊗[R] N)
  let Q := ModuleCat.of R (N ⧸ (J • (⊤ : Submodule R N)))
  let e : (ModuleCat.restrictScalars phi.hom).obj T ≅ Q :=
    ((restrictedScalarTowerModuleEquiv (R := R) (S := R ⧸ J) T).trans
      (TensorProduct.quotTensorEquivQuotSMul N J)).toModuleIso
  have hn := congrArg (fun f => f.hom (Submodule.Quotient.mk n))
    ((tilde.adjunction (R := R)).unit.naturality e.inv)
  change (tilde.adjunction (R := R)).unit.app
      ((ModuleCat.restrictScalars phi.hom).obj T) (e.inv (Submodule.Quotient.mk n)) =
    (moduleSpecΓFunctor (R := R)).map ((tilde.functor R).map e.inv)
      ((tilde.adjunction (R := R)).unit.app Q (Submodule.Quotient.mk n)) at hn
  have hq : e.inv (Submodule.Quotient.mk n) = (1 : R ⧸ J) ⊗ₜ[R] n := by
    change (TensorProduct.quotTensorEquivQuotSMul N J).symm (Submodule.Quotient.mk n) = _
    exact TensorProduct.quotTensorEquivQuotSMul_symm_mk J n
  have hr := tildePushforwardIso_globalValue phi T (e.inv (Submodule.Quotient.mk n))
  simp only [tildeCoefficientQuotientPushforwardIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, ModuleCat.comp_apply]
  change (tildePushforwardGlobalIso phi T).hom
    ((moduleSpecΓFunctor (R := R)).map (tildePushforwardIso phi T).hom
      ((moduleSpecΓFunctor (R := R)).map ((tilde.functor R).map e.inv)
        ((tilde.adjunction (R := R)).unit.app Q (Submodule.Quotient.mk n)))) = _
  exact (congrArg (fun x => (tildePushforwardGlobalIso phi T).hom
    ((moduleSpecΓFunctor (R := R)).map (tildePushforwardIso phi T).hom x)) hn.symm).trans
      (hr.trans hq)

end LinearStudy
