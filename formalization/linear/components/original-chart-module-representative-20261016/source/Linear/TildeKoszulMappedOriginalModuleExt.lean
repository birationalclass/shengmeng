module
public import Linear.TildeReflectsKoszulExact
public import Linear.TildeKoszulCoforkModuleExtIso
public import Linear.MappedChainPresentationOriginalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u s
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Retain the SAME original C and actual gamma,with the actual original
quotient cofork of the fixed affine Koszul. This is constructed data. -/
@[reducible]
def tildeKoszulMappedOriginalPresentation (R : CommRingCat.{s}) {r : ℕ} (H : Fin r → R)
    (F : A ⥤ (Spec R).Modules) [F.Additive] (C : ChainComplex A ℕ)
    (gamma : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅
      tildeFunctionKoszulComplex R H) :
    Σ C0 : ChainComplex A ℕ,Σ D : ChainComplex (Spec R).Modules ℕ,
      Σ _g : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C0) ≅ D,
        Σ Q : CokernelCofork (D.d 1 0),IsColimit Q :=
  ⟨C,tildeFunctionKoszulComplex R H,gamma,tildeKoszulOriginalCutCokernelCofork R H,
    tildeKoszulOriginalCutCokernelCoforkIsColimit R H⟩

/-- Explicit STATEMENT of the SAME original global Ext class's MODULE
representative. Derive positive module exactness from the actual original
augmentation;construct the coefficient cocycle preimage and native Ext
class. Only an actual coefficient iso is explicit at this generic boundary.
The original top-term application constructs it independently. -/
def tildeKoszulMappedOriginalModuleExtLaw (R : CommRingCat.{s}) {r : ℕ} (H : Fin r → R)
    (F : A ⥤ (Spec R).Modules) [F.Additive] [F.PreservesHomology]
    (C : ChainComplex A ℕ)
    (gamma : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅
      tildeFunctionKoszulComplex R H)
    (T : A) (e : cokernel (C.d 1 0) ≅ T) : Prop :=
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (ModuleCat.{s} R)
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteLimits_of_preservesHomology F
  letI := Functor.preservesFiniteColimits_of_preservesHomology F
  let p := tildeKoszulMappedOriginalPresentation R H F C gamma
  ∀ he : QuasiIso (originalChainCokernelTargetAugmentation C T e),
    letI : QuasiIso (originalChainCokernelTargetAugmentation p.1 T e) := he
    letI : QuasiIso (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H)) := mappedChainPresentationCoforkAugmentation_quasiIso F p T e
    let heK := tildeKoszul_moduleExact_of_coforkQuasiIso R H
    let theta := mappedChainPresentationAugmentationTargetIso F p T e
    let rho := tildeQuotientPushforwardIso R (Ideal.span (Set.range H))
    ∀ {M : A} (ell : ℕ) (N : ModuleCat.{s} R)
      (lambda : F.obj M ≅ (tilde.functor R).obj N)
      (a : C.X ell ⟶ M) (ha : C.d (ell+1) ell ≫ a = 0),
      let b := mappedChainPresentationOriginalTopFunctional F p ell a
      let hb := mappedChainPresentationOriginalTopFunctional_isCocycle F p ell a ha
      let eta := tildeKoszulIsoCocycleModuleExt R H heK ell N lambda b hb
      (Ext.mk₀ (rho.hom ≫ theta.inv)).comp
        (((originalChainTopExtClass C ell (originalChainCokernelTargetAugmentation C T e)
          a ha).mapExactFunctor F).comp (Ext.mk₀ lambda.hom) (add_zero _)) (zero_add _) =
        eta.mapExactFunctor (tilde.functor R)

theorem tildeKoszulMappedOriginalModuleExtLaw_proof (R : CommRingCat.{s}) {r : ℕ} (H : Fin r → R)
    (F : A ⥤ (Spec R).Modules) [F.Additive] [F.PreservesHomology]
    (C : ChainComplex A ℕ)
    (gamma : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅
      tildeFunctionKoszulComplex R H)
    (T : A) (e : cokernel (C.d 1 0) ≅ T) :
    tildeKoszulMappedOriginalModuleExtLaw R H F C gamma T e := by
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (ModuleCat.{s} R)
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  dsimp only [tildeKoszulMappedOriginalModuleExtLaw]
  intro he
  letI := he
  letI := Functor.preservesFiniteLimits_of_preservesHomology F
  letI := Functor.preservesFiniteColimits_of_preservesHomology F
  let p := tildeKoszulMappedOriginalPresentation R H F C gamma
  letI : QuasiIso (originalChainCokernelTargetAugmentation p.1 T e) := he
  letI : QuasiIso (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
    (tildeKoszulOriginalCutCokernelCofork R H)) := mappedChainPresentationCoforkAugmentation_quasiIso F p T e
  let heK := tildeKoszul_moduleExact_of_coforkQuasiIso R H
  let theta := mappedChainPresentationAugmentationTargetIso F p T e
  let rho := tildeQuotientPushforwardIso R (Ideal.span (Set.range H))
  intro M ell N lambda a ha
  let b := mappedChainPresentationOriginalTopFunctional F p ell a
  have hb := mappedChainPresentationOriginalTopFunctional_isCocycle F p ell a ha
  have hg := mappedChainPresentationOriginalExt_mapExactFunctor F p T e ell a ha
  have hm := tildeKoszulCoforkModuleExtIsoLaw_proof R H heK ell N lambda b hb
  dsimp only [tildeKoszulCoforkModuleExtIsoLaw] at hm
  change (Ext.mk₀ (rho.hom ≫ theta.inv)).comp
    (((originalChainTopExtClass C ell (originalChainCokernelTargetAugmentation C T e)
      a ha).mapExactFunctor F).comp (Ext.mk₀ lambda.hom) (add_zero _)) (zero_add _) = _
  have ht : (rho.hom ≫ theta.inv) ≫ (mappedChainPresentationAugmentationTargetIso F p T e).hom = rho.hom := by
    change (rho.hom ≫ theta.inv) ≫ theta.hom = rho.hom
    exact (Category.assoc rho.hom theta.inv theta.hom).trans ((congrArg (fun z => rho.hom ≫ z) theta.inv_hom_id).trans (Category.comp_id rho.hom))
  rw [hg,Ext.comp_assoc_of_third_deg_zero,Ext.mk₀_comp_mk₀_assoc,ht]
  exact hm

end LinearStudy
