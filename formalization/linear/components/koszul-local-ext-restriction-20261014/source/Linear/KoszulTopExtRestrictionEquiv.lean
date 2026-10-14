module
public import Linear.KoszulTopExtRepresentatives
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R] (n : ℕ)
variable (H : Fin (n+1) → R) (hreg : IsRegular R (List.ofFn H))

/-- Upgrade ACTUAL original Koszul Ext representatives to an R-linear
map,using pinned mathlib add_extMk and actual Ext push/scalar API. -/
def koszulTopExtRepresentativeLinearMap :
    Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R]
      Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) (ModuleCat.of R R) (n+1) where
  toFun := koszulTopExtRepresentative n H hreg
  map_add' L F :=
    ((functionKoszulResolution H hreg).add_extMk (ModuleCat.ofHom L) (ModuleCat.ofHom F)
      (n+2) rfl (koszulTopFunctional_isCocycle n H hreg L)
      (koszulTopFunctional_isCocycle n H hreg F)).symm
  map_smul' a L := by
    have hp := koszulTopExtRepresentative_push n H hreg L (a • LinearMap.id)
    have hs : (a • LinearMap.id : R →ₗ[R] R).comp L=a • L := by
      apply LinearMap.ext
      intro x
      rfl
    rw [hs] at hp
    exact hp.symm.trans (Ext.smul_eq_comp_mk₀ _ a).symm

/-- ORIGINAL coefficient restriction has EXACTLY the kernel of the
ACTUAL original derived Ext representative map. -/
theorem koszulTopExtRepresentativeLinearMap_kernel :
    LinearMap.ker (koszulTopExtRepresentativeLinearMap n H hreg)=
      LinearMap.ker (koszulTopFunctionalRestriction n H) := by
  apply Submodule.ext
  intro L
  change koszulTopExtRepresentative n H hreg L=0 ↔
    Ideal.Quotient.mk (Ideal.span (Set.range H)) (L (topKoszulGenerator (n+1)))=0
  exact (koszulTopExtRepresentative_eq_zero_iff n H hreg L).trans
    Ideal.Quotient.eq_zero_iff_mem.symm

/-- ACTUAL ring Ext of the ORIGINAL regular Koszul cut is the ORIGINAL
cut ring. Constructed via ACTUAL representative and restriction maps,
not an assumed Ext model. Global sheaf Ext comparison remains separate. -/
def koszulTopExtRestrictionEquiv :
    Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) (ModuleCat.of R R) (n+1) ≃ₗ[R]
      R ⧸ Ideal.span (Set.range H) :=
  ((koszulTopExtRepresentativeLinearMap n H hreg).quotKerEquivOfSurjective
      (koszulTopExtRepresentative_surjective n H hreg)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (koszulTopExtRepresentativeLinearMap_kernel n H hreg)).trans
      ((koszulTopFunctionalRestriction n H).quotKerEquivOfSurjective
        (koszulTopFunctionalRestriction_surjective n H)))

/-- The ACTUAL original Ext representative is sent to its ORIGINAL
coefficient reduced modulo the ORIGINAL equation ideal. -/
theorem koszulTopExtRestrictionEquiv_representative
    (L : Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R))) :
    koszulTopExtRestrictionEquiv n H hreg (koszulTopExtRepresentative n H hreg L)=
      Ideal.Quotient.mk (Ideal.span (Set.range H)) (L (topKoszulGenerator (n+1))) := by
  let T := koszulTopExtRepresentativeLinearMap n H hreg
  let eT := T.quotKerEquivOfSurjective (koszulTopExtRepresentative_surjective n H hreg)
  have hh : eT.symm (koszulTopExtRepresentative n H hreg L)=Submodule.Quotient.mk L := by
    change eT.symm (eT (Submodule.Quotient.mk L)) = _
    exact eT.symm_apply_apply _
  change ((koszulTopFunctionalRestriction n H).quotKerEquivOfSurjective
    (koszulTopFunctionalRestriction_surjective n H))
    ((Submodule.quotEquivOfEq _ _ (koszulTopExtRepresentativeLinearMap_kernel n H hreg))
      (eT.symm (koszulTopExtRepresentative n H hreg L))) = _
  rw [hh,Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- Push the ACTUAL ordered-top-coordinate Ext class along ORIGINAL a.
Its image under the CONSTRUCTED ACTUAL ring Ext equivalence is a(1)
modulo ORIGINAL (H),the local coefficient-restriction computation.
The original GLOBAL sheaf extension/connecting class remains separate. -/
theorem koszulTopExtRestrictionEquiv_pushGenerator (a : R →ₗ[R] R) :
    koszulTopExtRestrictionEquiv n H hreg
      ((koszulTopExtRepresentative n H hreg (topKoszulCoordinate (n+1))).comp
        (Ext.mk₀ (ModuleCat.ofHom a)) (add_zero _)) =
      Ideal.Quotient.mk (Ideal.span (Set.range H)) (a 1) := by
  rw [koszulTopExtRepresentative_push,koszulTopExtRestrictionEquiv_representative]
  simp only [LinearMap.comp_apply,topKoszulCoordinate_generator]

end LinearStudy
