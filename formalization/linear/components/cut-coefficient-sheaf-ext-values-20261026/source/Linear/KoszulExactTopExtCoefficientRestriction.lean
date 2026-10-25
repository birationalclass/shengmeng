module
public import Linear.KoszulExactTopExtCoefficients
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u
variable {R : Type u} [CommRing R] (n : ℕ) (H : Fin (n+1) → R)
variable (he : ∀ j : ℕ, 0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)

/-- The actual arbitrary-N derived MODULE Ext representative map is
R-linear, using native add_extMk and actual coefficient push/scalar APIs. -/
def koszulExactTopExtCoefficientRepresentativeLinearMap (N : ModuleCat.{u} R) :
    ((⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) →ₗ[R]
      Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (n+1) where
  toFun := koszulExactTopExtCoefficientRepresentative n H he N
  map_add' L F :=
    ((functionKoszulResolutionOfExact H he).add_extMk (ModuleCat.ofHom L) (ModuleCat.ofHom F)
      (n+2) rfl (koszulExactTopCoefficient_isCocycle n H he N L)
      (koszulExactTopCoefficient_isCocycle n H he N F)).symm
  map_smul' a L := by
    have hp := koszulExactTopExtCoefficientRepresentative_push n H he N N L (a • LinearMap.id)
    have hs : (a • LinearMap.id : N →ₗ[R] N).comp L = a • L := by
      apply LinearMap.ext
      intro x
      rfl
    rw [hs] at hp
    exact hp.symm.trans (Ext.smul_eq_comp_mk₀ _ a).symm

/-- ACTUAL original derived Ext representative and original N/IN
restriction have precisely the same kernel. -/
theorem koszulExactTopExtCoefficientRepresentativeLinearMap_kernel (N : ModuleCat.{u} R) :
    LinearMap.ker (koszulExactTopExtCoefficientRepresentativeLinearMap n H he N) =
      LinearMap.ker (koszulTopHomCoefficientRestriction (N := N) n H) := by
  apply Submodule.ext
  intro L
  change koszulExactTopExtCoefficientRepresentative n H he N L = 0 ↔
    koszulTopHomCoefficientRestriction (N := N) n H L = 0
  exact koszulExactTopExtCoefficientRepresentative_eq_zero_iff n H he N L

/-- CONSTRUCT the ACTUAL derived MODULE Ext equivalence with original
N/IN from the SAME original Koszul representative and restriction maps.
No coefficient regularity/free/flat/invertible/CM or Ext-iso premise.
Positive exactness of the source is kept explicit and is DERIVED for
the original cut by the existing projective-cut construction. -/
def koszulExactTopExtCoefficientRestrictionEquiv (N : ModuleCat.{u} R) :
    Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (n+1) ≃ₗ[R]
      N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)) :=
  ((koszulExactTopExtCoefficientRepresentativeLinearMap n H he N).quotKerEquivOfSurjective
      (koszulExactTopExtCoefficientRepresentative_surjective n H he N)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (koszulExactTopExtCoefficientRepresentativeLinearMap_kernel n H he N)).trans
      ((koszulTopHomCoefficientRestriction (N := N) n H).quotKerEquivOfSurjective
        (koszulTopHomCoefficientRestriction_surjective n H)))

/-- SAME original actual derived class [L] maps to original L(v_r) mod IN. -/
theorem koszulExactTopExtCoefficientRestrictionEquiv_representative
    (N : ModuleCat.{u} R) (L : (⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) :
    koszulExactTopExtCoefficientRestrictionEquiv n H he N
      (koszulExactTopExtCoefficientRepresentative n H he N L) =
      Submodule.Quotient.mk (L (topKoszulGenerator (n+1))) := by
  let T := koszulExactTopExtCoefficientRepresentativeLinearMap n H he N
  let eT := T.quotKerEquivOfSurjective (koszulExactTopExtCoefficientRepresentative_surjective n H he N)
  have hh : eT.symm (koszulExactTopExtCoefficientRepresentative n H he N L) =
      Submodule.Quotient.mk L := by
    change eT.symm (eT (Submodule.Quotient.mk L)) = _
    exact eT.symm_apply_apply _
  change ((koszulTopHomCoefficientRestriction (N := N) n H).quotKerEquivOfSurjective
    (koszulTopHomCoefficientRestriction_surjective n H))
    ((Submodule.quotEquivOfEq _ _
      (koszulExactTopExtCoefficientRepresentativeLinearMap_kernel n H he N))
      (eT.symm (koszulExactTopExtCoefficientRepresentative n H he N L))) = _
  rw [hh,Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- Push the SAME actual ordered-top MODULE Ext class along ORIGINAL
a:R->N. Under the constructed actual N-valued Ext equivalence it is
original a(1) mod IN. N need not be locally free or invertible. This is
not a claim about the still-open original GLOBAL sheaf extension class. -/
theorem koszulExactTopExtCoefficientRestrictionEquiv_pushGenerator
    (N : ModuleCat.{u} R) (a : R →ₗ[R] N) :
    koszulExactTopExtCoefficientRestrictionEquiv n H he N
      ((koszulExactTopExtCoefficientRepresentative n H he (ModuleCat.of R R)
        (topKoszulCoordinate (n+1))).comp
          (Ext.mk₀ (ModuleCat.ofHom a)) (add_zero _)) =
      Submodule.Quotient.mk (a 1) := by
  rw [koszulExactTopExtCoefficientRepresentative_push,
    koszulExactTopExtCoefficientRestrictionEquiv_representative]
  simp only [LinearMap.comp_apply,topKoszulCoordinate_generator]

end LinearStudy
