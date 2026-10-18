module
public import Linear.TildeCoefficientQuotientGeometricUnit
public import Linear.AffineKoszulHomCoefficientRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local irreducible] affineTildeTensorPullbackIso
  tildeCoefficientQuotientPushforwardIso

/-- ACTUAL original internal-Hom Koszul top sequence ends in ACTUAL
pushforward of the ORIGINAL geometric cut pullback i^*(tilde N).
Original N arbitrary; no regularity/FP/free/flat/invertibility/CM inputs. -/
def affineKoszulHomGeometricRestrictionPresentation (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    ShortComplex (Spec R).Modules where
  X₁ := (affineKoszulHomCoefficientRestrictionPresentation R N n H).X₁
  X₂ := (affineKoszulHomCoefficientRestrictionPresentation R N n H).X₂
  X₃ := (Scheme.Modules.pushforward
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
      ((Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
          (tilde N))
  f := (affineKoszulHomCoefficientRestrictionPresentation R N n H).f
  g := (affineKoszulHomCoefficientRestrictionPresentation R N n H).g ≫
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).map
        (affineTildeTensorPullbackIso R
          (CommRingCat.of (R ⧸ Ideal.span (Set.range H))) N).inv
  zero := by
    rw [← Category.assoc,
      (affineKoszulHomCoefficientRestrictionPresentation R N n H).zero, zero_comp]

/-- Construct comparison of SAME original tensor-cut and geometric-cut
short complexes using the PROVED actual geometric pullback iso. -/
def affineKoszulHomGeometricRestrictionPresentationIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    affineKoszulHomCoefficientRestrictionPresentation R N n H ≅
      affineKoszulHomGeometricRestrictionPresentation R N n H := by
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).mapIso
        (affineTildeTensorPullbackIso R
          (CommRingCat.of (R ⧸ Ideal.span (Set.range H))) N).symm)
    (by simp only [affineKoszulHomGeometricRestrictionPresentation,
      Iso.refl_hom, Category.id_comp, Category.comp_id])
    (by simp only [affineKoszulHomGeometricRestrictionPresentation,
      Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Iso.symm_hom])

/-- Exactness for SAME actual internal-Hom sequence with the ORIGINAL
geometric pullback coefficient. No exactness certificate is a premise. -/
theorem affineKoszulHomGeometricRestrictionPresentation_exact (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulHomGeometricRestrictionPresentation R N n H).Exact :=
  ShortComplex.exact_of_iso (affineKoszulHomGeometricRestrictionPresentationIso R N n H)
    (affineKoszulHomCoefficientRestrictionPresentation_exact R N n H)

/-- ORIGINAL coefficient restriction is epi onto ORIGINAL i_*i^*(tilde N). -/
theorem affineKoszulHomGeometricRestrictionPresentation_epi (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    Epi (affineKoszulHomGeometricRestrictionPresentation R N n H).g := by
  letI := affineKoszulHomCoefficientRestrictionPresentation_epi R N n H
  change Epi ((affineKoszulHomCoefficientRestrictionPresentation R N n H).g ≫
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).map
        (affineTildeTensorPullbackIso R
          (CommRingCat.of (R ⧸ Ideal.span (Set.range H))) N).inv)
  infer_instance

/-- SAME original Koszul restriction is EXACTLY ordered-top evaluation
followed by the ACTUAL ORIGINAL geometric restriction unit. This proves
the actual MORPHISM diagram; an object iso alone is not used as a proof. -/
theorem affineKoszulHomGeometricRestrictionPresentation_restriction
    (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom ≫
      (affineKoszulHomGeometricRestrictionPresentation R N n H).g =
    (tilde.functor R).map
      (ModuleCat.ofHom (koszulTopHomCoefficientEquiv (N := N) n).toLinearMap) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).unit.app
          (tilde N) := by
  change (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom ≫
    ((affineKoszulHomCoefficientRestrictionPresentation R N n H).g ≫ _) = _
  rw [← Category.assoc, affineKoszulHomCoefficientRestrictionPresentation_restriction]
  change (tilde.functor R).map
      (ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)) ≫
    (tildeCoefficientQuotientPushforwardIso R (Ideal.span (Set.range H)) N).hom ≫
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).map
        (affineTildeTensorPullbackIso R
          (CommRingCat.of (R ⧸ Ideal.span (Set.range H))) N).inv = _
  have hr : ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H) =
      ModuleCat.ofHom (koszulTopHomCoefficientEquiv (N := N) n).toLinearMap ≫
        ModuleCat.ofHom (Ideal.span (Set.range H) • (⊤ : Submodule R N)).mkQ := rfl
  rw [hr, Functor.map_comp, Category.assoc]
  change (tilde.functor R).map
      (ModuleCat.ofHom (koszulTopHomCoefficientEquiv (N := N) n).toLinearMap) ≫
    ((tilde.functor R).map (ModuleCat.ofHom (Ideal.span (Set.range H) • (⊤ : Submodule R N)).mkQ) ≫
      (tildeCoefficientQuotientGeometricPullbackPushforwardIso R (Ideal.span (Set.range H)) N).hom) = _
  rw [tildeCoefficientQuotientGeometricPullbackPushforwardIso_unit]

end LinearStudy
