module
public import Linear.TildeKoszulMappedOriginalModuleExt
public import Linear.MappedChainPresentationTopCoefficientIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u s
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (R : CommRingCat.{s}) {r : ℕ} (H : Fin r → R)
variable (F : A ⥤ (Spec R).Modules) [F.Additive] [F.PreservesHomology]
variable (C : ChainComplex A ℕ)
variable (gamma : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅
  tildeFunctionKoszulComplex R H)

/-- Construct a coefficient frame from the ACTUAL original top-term iso
and ACTUAL whole chart iso. No independent coordinate-frame equality is
assumed. Such independently prescribed frames still require comparison. -/
def tildeKoszulOriginalTopCoefficientIso {M : A} (phi : C.X r ≅ M) :
    F.obj M ≅ (tilde.functor R).obj ((koszulComplex (Fintype.linearCombination R H)).X r) :=
  (mappedChainPresentationOriginalTopIso F
    (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi).symm

/-- In this actual induced frame,the SAME original top functional has
MODULE preimage identity. Hom faithfulness and actual iso cancellation
prove the statement;no module functional formula is a hypothesis. -/
theorem tildeKoszulOriginalTopFunctional_preimage_id {M : A} (phi : C.X r ≅ M) :
    tildeActualFunctionalPreimage R
      (mappedChainPresentationOriginalTopFunctional F
        (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi.hom ≫
          (tildeKoszulOriginalTopCoefficientIso R H F C gamma phi).hom) =
      𝟙 ((koszulComplex (Fintype.linearCombination R H)).X r) := by
  apply (tilde.functor R).map_injective
  exact (tildeActualFunctionalPreimage_map R _).trans
    ((mappedChainPresentationOriginalTopIso_normalize F
      (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi).trans
        ((tilde.functor R).map_id _).symm)

/-- The resulting actual MODULE class is native extMk of identity on
its top exterior module. This statement is about the actual induced
frame,not an unproved equality with a separately fixed conventional frame. -/
theorem tildeKoszulOriginalTopModuleExt_eq_identity
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    {M : A} (phi : C.X r ≅ M) (hphi : C.d (r+1) r ≫ phi.hom = 0) :
    tildeKoszulIsoCocycleModuleExt R H he r
      ((koszulComplex (Fintype.linearCombination R H)).X r)
      (tildeKoszulOriginalTopCoefficientIso R H F C gamma phi)
      (mappedChainPresentationOriginalTopFunctional F
        (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi.hom)
      (mappedChainPresentationOriginalTopFunctional_isCocycle F
        (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi.hom hphi) =
    (functionKoszulResolutionOfExact H he).extMk (𝟙 _) (r+1) rfl
      (by
        have ht := tildeActualFunctionalPreimage_isCocycle R
          (koszulComplex (Fintype.linearCombination R H)) r
          ((koszulComplex (Fintype.linearCombination R H)).X r)
          (mappedChainPresentationOriginalTopFunctional F
            (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi.hom ≫
              (tildeKoszulOriginalTopCoefficientIso R H F C gamma phi).hom)
          (tildeKoszulIsoCocycle_isCocycle R H r _
            (tildeKoszulOriginalTopCoefficientIso R H F C gamma phi) _
            (mappedChainPresentationOriginalTopFunctional_isCocycle F
              (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi.hom hphi))
        exact (congrArg (fun z => (koszulComplex (Fintype.linearCombination R H)).d (r+1) r ≫ z)
          (tildeKoszulOriginalTopFunctional_preimage_id R H F C gamma phi)).symm.trans ht) := by
  let P := functionKoszulResolutionOfExact H he
  let b := mappedChainPresentationOriginalTopFunctional F
    (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi.hom
  have hb := mappedChainPresentationOriginalTopFunctional_isCocycle F
    (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi.hom hphi
  let ac := b ≫ (tildeKoszulOriginalTopCoefficientIso R H F C gamma phi).hom
  have hid := tildeKoszulOriginalTopFunctional_preimage_id R H F C gamma phi
  have hf := tildeActualFunctionalPreimage_isCocycle R P.complex r (P.complex.X r) ac
    (tildeKoszulIsoCocycle_isCocycle R H r _
      (tildeKoszulOriginalTopCoefficientIso R H F C gamma phi) b hb)
  have hg : P.complex.d (r+1) r ≫ 𝟙 (P.complex.X r) = 0 :=
    (congrArg (fun z => P.complex.d (r+1) r ≫ z) hid).symm.trans hf
  have hc : ∀ (f g : P.complex.X r ⟶ P.complex.X r)
      (hf : P.complex.d (r+1) r ≫ f = 0) (hg : P.complex.d (r+1) r ≫ g = 0),
      f = g → P.extMk f (r+1) rfl hf = P.extMk g (r+1) rfl hg := by
    intro f g hf hg heq
    subst g
    rfl
  exact hc _ _ hf hg hid

/-- Explicit normalization STATEMENT at the abstract module/chart
boundary. Keeping this formula abstract avoids expanding actual native
localization ring structures during geometric specialization. -/
def tildeKoszulOriginalTopModuleFrameLaw {M : A} (phi : C.X r ≅ M) : Prop :=
    tildeActualFunctionalPreimage R
      (mappedChainPresentationOriginalTopFunctional F
        (tildeKoszulMappedOriginalPresentation R H F C gamma) r phi.hom ≫
          (tildeKoszulOriginalTopCoefficientIso R H F C gamma phi).hom) =
      𝟙 ((koszulComplex (Fintype.linearCombination R H)).X r)

/-- Prove the explicit normalization law by the SAME original Hom
preimage and actual chart/top-term isos. No formula is a premise. -/
theorem tildeKoszulOriginalTopModuleFrameLaw_proof {M : A} (phi : C.X r ≅ M) :
    tildeKoszulOriginalTopModuleFrameLaw R H F C gamma phi :=
  tildeKoszulOriginalTopFunctional_preimage_id R H F C gamma phi

end LinearStudy
