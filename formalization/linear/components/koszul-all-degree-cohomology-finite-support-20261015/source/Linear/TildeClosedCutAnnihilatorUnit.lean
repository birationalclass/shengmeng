module
public import Linear.TildeCoefficientQuotientGeometricUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- ORIGINAL ideal annihilation implies ORIGINAL I N is zero;no finiteness
of the original coefficient module is needed. -/
theorem originalIdeal_smul_top_eq_bot_of_annihilator (R : CommRingCat.{u})
    (I : Ideal R) (N : ModuleCat.{u} R) (hAnn : I ≤ Module.annihilator R N) :
    I • (⊤ : Submodule R N) = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x hx
  exact (Module.mem_annihilator.mp (hAnn ha)) x

attribute [local irreducible] tildeCoefficientQuotientGeometricPullbackPushforwardIso

/-- ACTUAL ORIGINAL geometric closed-cut unit is an iso for ANY original
associated coefficient annihilated by ORIGINAL I. Construct it from the
PROVED original quotient/unit comparison;no desired support/unit certificate. -/
def tildeClosedCutAnnihilatorUnitIso (R : CommRingCat.{u}) (I : Ideal R)
    (N : ModuleCat.{u} R) (hAnn : I ≤ Module.annihilator R N) :
    tilde N ≅ (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj (tilde N)) :=
  (tilde.functor R).mapIso
      ((I • (⊤ : Submodule R N)).quotEquivOfEqBot
        (originalIdeal_smul_top_eq_bot_of_annihilator R I N hAnn)).symm.toModuleIso ≪≫
    tildeCoefficientQuotientGeometricPullbackPushforwardIso R I N

/-- This SAME constructed iso has hom EXACTLY the ACTUAL original unit;
an object iso is not substituted for geometric morphism compatibility. -/
theorem tildeClosedCutAnnihilatorUnitIso_unit (R : CommRingCat.{u}) (I : Ideal R)
    (N : ModuleCat.{u} R) (hAnn : I ≤ Module.annihilator R N) :
    (tildeClosedCutAnnihilatorUnitIso R I N hAnn).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).unit.app (tilde N) := by
  have hf : ((I • (⊤ : Submodule R N)).quotEquivOfEqBot
        (originalIdeal_smul_top_eq_bot_of_annihilator R I N hAnn)).symm.toModuleIso.hom =
      ModuleCat.ofHom (I • (⊤ : Submodule R N)).mkQ := by
    apply ModuleCat.hom_ext
    exact Submodule.coe_quotEquivOfEqBot_symm _ _
  simp only [tildeClosedCutAnnihilatorUnitIso,Iso.trans_hom,Functor.mapIso_hom]
  rw [hf,tildeCoefficientQuotientGeometricPullbackPushforwardIso_unit]

end LinearStudy
