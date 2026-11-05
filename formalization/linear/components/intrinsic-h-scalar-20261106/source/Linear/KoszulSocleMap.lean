module

public import Linear.KoszulComparison
public import Linear.KoszulHomotopyTop

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace LinearStudy
variable {R : Type*} [CommRing R]

theorem socleScalarMap_kernel (I J : Ideal R) (a : R ⧸ I)
    (ha : a ∈ (J.map (Ideal.Quotient.mk I)).annihilator) :
    J ≤ (LinearMap.id.smulRight a : R →ₗ[R] R ⧸ I).ker := by
  intro r hr
  change r • a = 0
  have h := Submodule.mem_annihilator.mp ha
    (Ideal.Quotient.mk I r) (Ideal.mem_map_of_mem _ hr)
  change a * Ideal.Quotient.mk I r = 0 at h
  simpa [Algebra.smul_def, mul_comm] using h

def socleQuotientMap (I J : Ideal R) (a : R ⧸ I)
    (ha : a ∈ (J.map (Ideal.Quotient.mk I)).annihilator) :
    (R ⧸ J) →ₗ[R] (R ⧸ I) :=
  J.liftQ (LinearMap.id.smulRight a) (socleScalarMap_kernel I J a ha)

theorem socleQuotientMap_apply_mk (I J : Ideal R) (a : R ⧸ I)
    (ha : a ∈ (J.map (Ideal.Quotient.mk I)).annihilator) (r : R) :
    socleQuotientMap I J a ha (Ideal.Quotient.mk J r) = r • a := rfl

end LinearStudy
