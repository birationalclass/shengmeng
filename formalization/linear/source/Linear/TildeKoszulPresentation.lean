module
public import Linear.TildeKoszulStructureAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The actual first two Koszul terms present the pushed-forward cut
structure sheaf, using the original quotient augmentation. -/
def tildeKoszulPresentation (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    ShortComplex (Spec R).Modules where
  X₁ := tilde (ModuleCat.of R (⋀[R]^1 (Fin r → R)))
  X₂ := tilde (ModuleCat.of R (⋀[R]^0 (Fin r → R)))
  X₃ := (Scheme.Modules.pushforward
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
      (SheafOfModules.unit.{u}
        (Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range H)))).ringCatSheaf)
  f := (tilde.functor R).map
    (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) 0))
  g := (tilde.functor R).map (ModuleCat.ofHom (functionKoszulAugmentation H)) ≫
    (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom
  zero := by
    have h : ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) 0) ≫
        ModuleCat.ofHom (functionKoszulAugmentation H) = 0 :=
      ModuleCat.hom_ext (functionKoszulAugmentation_comp_d H)
    calc
      _ = ((tilde.functor R).map
          (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) 0)) ≫
          (tilde.functor R).map (ModuleCat.ofHom (functionKoszulAugmentation H))) ≫
          (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom :=
        (Category.assoc _ _ _).symm
      _ = (tilde.functor R).map (0 : ModuleCat.of R (⋀[R]^1 (Fin r → R)) ⟶
          ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) ≫
          (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom :=
        congrArg (fun a => a ≫ (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom)
          ((Functor.map_comp _ _ _).symm.trans (congrArg (tilde.functor R).map h))
      _ = 0 := by simp only [Functor.map_zero, zero_comp]

/-- Actual native sheaf exactness of this presentation holds for every
original list of equations; no regular-sequence input is needed here. -/
theorem tildeKoszulPresentation_exact (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    (tildeKoszulPresentation R H).Exact := by
  letI := tilde_functor_preservesHomology R
  have h := (functionKoszulAugmentation_exact H).map (tilde.functor R)
  apply (ShortComplex.exact_iff_of_iso ?_).mp h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (tildeQuotientPushforwardIso R (Ideal.span (Set.range H)))
      (by simp [tildeKoszulPresentation]; rfl) (by simp [tildeKoszulPresentation])

/-- The original degree-zero quotient map is surjective on its actual
exterior-power source, not merely on an abstract identified copy of R. -/
theorem functionKoszulAugmentation_surjective (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) : Function.Surjective (functionKoszulAugmentation H) := by
  intro v
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective v
  refine ⟨(exteriorPower.zeroEquiv R (Fin r → R)).symm a,?_⟩
  change Ideal.Quotient.mk _ ((exteriorPower.zeroEquiv R _)
    ((exteriorPower.zeroEquiv R _).symm a)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The native structure-sheaf presentation ends in an epimorphism. -/
theorem tildeKoszulPresentation_epi (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    Epi (tildeKoszulPresentation R H).g := by
  letI := tilde_functor_preservesHomology R
  letI : Epi (ModuleCat.ofHom (functionKoszulAugmentation H)) :=
    (ModuleCat.epi_iff_surjective _).mpr (functionKoszulAugmentation_surjective R H)
  change Epi ((tilde.functor R).map (ModuleCat.ofHom (functionKoszulAugmentation H)) ≫
    (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom)
  infer_instance

end LinearStudy
