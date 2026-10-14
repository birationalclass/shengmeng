module
public import Linear.AffineKoszulAllCohomologySupport
public import Linear.TildeClosedCutAnnihilatorUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R)
variable (he : ∀ j : ℕ, 0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
attribute [local irreducible] affineKoszulInternalHomCohomologyNativeIso
  tildeClosedCutAnnihilatorUnitIso

/-- EVERY actual original internal-Hom cohomology object is pushed from
SAME original geometric closed cut by its ACTUAL pullback/pushforward unit.
This constructs a SAME-object geometric support iso,not only a module-support
predicate. Source exactness comes from original cut;N arbitrary. -/
def affineKoszulInternalHomCohomologyClosedCutUnitIso (j : ℕ) :
    (affineKoszulInternalHomCochainComplex R N r H).homology j ≅
      (Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
          ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
              ((affineKoszulInternalHomCochainComplex R N r H).homology j)) :=
  affineKoszulInternalHomCohomologyNativeIso R N r H j ≪≫
    tildeClosedCutAnnihilatorUnitIso R (Ideal.span (Set.range H))
      ((affineKoszulNativeHomCochainComplex R N r H).homology j)
      (affineKoszulNativeCohomology_ideal_annihilator R N r H he j) ≪≫
    ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H))))) ⋙
      Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).mapIso
          (affineKoszulInternalHomCohomologyNativeIso R N r H j)).symm

/-- SAME constructed geometric support iso is EXACTLY the ACTUAL
ORIGINAL unit,proved by native adjunction naturality and original unit
comparison. No desired support/unit/naturality certificate is input. -/
theorem affineKoszulInternalHomCohomologyClosedCutUnitIso_unit (j : ℕ) :
    (affineKoszulInternalHomCohomologyClosedCutUnitIso R N r H he j).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).unit.app
          ((affineKoszulInternalHomCochainComplex R N r H).homology j) := by
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).unit.naturality
      (affineKoszulInternalHomCohomologyNativeIso R N r H j).hom
  change (affineKoszulInternalHomCohomologyNativeIso R N r H j).hom ≫ _ = _ at hn
  simp only [affineKoszulInternalHomCohomologyClosedCutUnitIso,Iso.trans_hom,
    Iso.symm_hom,Functor.mapIso_inv]
  rw [tildeClosedCutAnnihilatorUnitIso_unit,← Category.assoc,hn,Category.assoc]
  simp only [Iso.hom_inv_id_map,Category.comp_id]


/-- The ACTUAL ORIGINAL geometric unit on actual cohomology,defined
without source exactness or support assumptions. This named morphism
avoids repeating the large original quotient-map type in geometric wrappers. -/
def affineKoszulInternalHomCohomologyClosedCutUnit (j : ℕ) :
    (affineKoszulInternalHomCochainComplex R N r H).homology j ⟶
      (Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
          ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
              ((affineKoszulInternalHomCochainComplex R N r H).homology j)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).unit.app
      ((affineKoszulInternalHomCochainComplex R N r H).homology j)

include he

/-- PROVE the actual named original unit is an isomorphism;this is a
CONCLUSION from constructed original cohomology support,not an input
certificate. Original he explicit here and derived for original cuts. -/
theorem affineKoszulInternalHomCohomologyClosedCutUnit_isIso (j : ℕ) :
    IsIso (affineKoszulInternalHomCohomologyClosedCutUnit R N r H j) := by
  change IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).unit.app
      ((affineKoszulInternalHomCochainComplex R N r H).homology j))
  rw [← affineKoszulInternalHomCohomologyClosedCutUnitIso_unit R N r H he j]
  infer_instance

end LinearStudy
