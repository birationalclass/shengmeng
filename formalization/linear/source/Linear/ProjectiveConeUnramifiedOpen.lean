module
public import Linear.ProjectiveGenericUnramified
public import Linear.GenericUnramifiedOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- A nonempty principal open of the actual affine cone where the actual
homogeneous-coordinate map is formally unramified over its source.
This does not yet descend to a projective chart or give an entire fiber. -/
theorem projectiveCoordinateDomainMap_exists_nonzero_unramified_open
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    ∃ a : CoordinateRing n ⧸ V.ideal.toIdeal, a ≠ 0 ∧
      ((algebraMap _ (Localization.Away a)).comp
        (projectiveCoordinateDomainMap f V hq hf hV).toRingHom).FormallyUnramified := by
  letI := V.prime
  exact ringHom_fraction_exists_nonzero_unramified_open
    (projectiveCoordinateDomainMap f V hq hf hV).toRingHom
    (projectiveCoordinateDomainMap_finiteType f V hq hf hV).essFiniteType
    (projectiveCoordinateDomainMap_fraction_comp_formallyUnramified f V hq hf hV)

end LinearStudy
