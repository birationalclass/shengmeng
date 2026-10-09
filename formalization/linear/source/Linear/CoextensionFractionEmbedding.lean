module
public import Linear.CoextensionFractionNaturality
public import Linear.FieldCoextensionRankOne
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Choose the proved rank-one isomorphism for the actual original
fraction-field extension. Finiteness is derived from the finite algebra. -/
def coextensionFractionRankOneIso :
    (ModuleCat.coextendScalars (algebraMap (FractionRing R) (FractionRing S))).obj
      (ModuleCat.of (FractionRing R) (FractionRing R)) ≃ₗ[FractionRing S] FractionRing S :=
  (Classical.choice (fieldCoextensionDual_exists_equiv
    (K := FractionRing R) (L := FractionRing S))).symm

/-- Embed the original native finite dual into the ACTUAL original
fraction field, by the constructed extension and the proved field duality. -/
def coextensionFractionEmbedding :
    (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) →ₗ[S]
      FractionRing S :=
  restrictedAlgebraModuleEquiv.toLinearMap.comp
    (((ModuleCat.restrictScalars (algebraMap S (FractionRing S))).map
      (ModuleCat.ofHom (coextensionFractionRankOneIso (R := R) (S := S)).toLinearMap)).hom.comp
        (coextensionFractionNativeLinear (R := R) (S := S)))

theorem coextensionFractionEmbedding_injective :
    Function.Injective (coextensionFractionEmbedding (R := R) (S := S)) := by
  change Function.Injective (fun ell :
      (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) =>
    (coextensionFractionRankOneIso (R := R) (S := S))
      (coextensionFractionNativeLinear (R := R) (S := S) ell))
  exact (coextensionFractionRankOneIso (R := R) (S := S)).injective.comp
    (coextensionFractionNativeLinear_injective (R := R) (S := S))

end LinearStudy
