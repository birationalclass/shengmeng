module
public import Linear.TildeQuotientPushforward
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- The target of the actual affine Koszul is the actual cut structure
sheaf pushed forward, concentrated in degree zero. -/
def tildeKoszulStructureTargetIso (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    tildeFunctionKoszulQuotientComplex R H ≅
      (ChainComplex.single₀ (Spec R).Modules).obj
        ((Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
            (SheafOfModules.unit.{u}
              (Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range H)))).ringCatSheaf)) :=
  (HomologicalComplex.singleMapHomologicalComplex (tilde.functor R)
    (ComplexShape.down ℕ) 0).app (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) ≪≫
      (ChainComplex.single₀ (Spec R).Modules).mapIso
        (tildeQuotientPushforwardIso R (Ideal.span (Set.range H)))

/-- The native sheaf augmentation to the actual cut structure sheaf. -/
def tildeKoszulStructureAugmentation (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    tildeFunctionKoszulComplex R H ⟶
      (ChainComplex.single₀ (Spec R).Modules).obj
        ((Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
            (SheafOfModules.unit.{u}
              (Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range H)))).ringCatSheaf)) :=
  tildeFunctionKoszulAugmentation R H ≫ (tildeKoszulStructureTargetIso R H).hom

/-- Its quasi-isomorphism is derived from original Koszul exactness and
the constructed target isomorphism, not supplied as a bridge hypothesis. -/
theorem tildeKoszulStructureAugmentation_quasiIso (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j) :
    QuasiIso (tildeKoszulStructureAugmentation R H) := by
  letI : QuasiIso (tildeFunctionKoszulAugmentation R H) :=
    tilde_functionKoszul_augmentation_quasiIso R H he
  unfold tildeKoszulStructureAugmentation
  infer_instance

end LinearStudy
