module
public import Linear.IntegerShiftedFreeHomCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J : Type*} [Field K] [CommRing S] [Algebra K S]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (c : (I → S) →ₗ[S] (J → S))

/-- Precomposition with the ACTUAL original relation map is multiplication
by its ACTUAL transpose-entry matrix in canonical original free Hom
coordinates. This is a proved identity,not the definition of c*. -/
theorem integerShiftedFreeDual_relation_coordinates
    (φ : Module.Dual S (J → S)) (i : I) :
    integerShiftedFreeDualCoordinates (K := K) (φ.comp c) i =
      ∑ j, integerShiftedFreeMapEntry c i j * integerShiftedFreeDualCoordinates (K := K) φ j := by
  rw [integerShiftedFreeDualCoordinates_apply]
  simpa only [LinearMap.comp_apply,LinearMap.pi_apply,integerShiftedFreeMapEntry,
    integerShiftedFreeDualCoordinates_apply]
    using integerShiftedFreeMap_apply (LinearMap.pi (fun _ : Unit => φ)) (c (Pi.single i 1)) ()

/-- Membership in the ACTUAL original dual relation kernel is exactly
vanishing of the original polynomial relation sums on all original
coordinate basis vectors. No kernel/matrix identity is a premise. -/
theorem integerShiftedFreeDual_kernel_iff_relations (φ : Module.Dual S (J → S)) :
    φ ∈ LinearMap.ker c.dualMap ↔
      ∀ i, ∑ j, integerShiftedFreeMapEntry c i j *
        integerShiftedFreeDualCoordinates (K := K) φ j = 0 := by
  rw [LinearMap.mem_ker,LinearMap.dualMap_apply']
  constructor
  · intro h i
    have he := congrArg (fun f : Module.Dual S (I → S) =>
      integerShiftedFreeDualCoordinates (K := K) f i) h
    simpa only [integerShiftedFreeDual_relation_coordinates,map_zero,Pi.zero_apply] using he
  · intro h
    apply (integerShiftedFreeDualCoordinates (K := K) (S := S) (J := I)).injective
    ext i
    simpa only [map_zero,Pi.zero_apply] using
      (integerShiftedFreeDual_relation_coordinates c φ i).trans (h i)

end LinearStudy
