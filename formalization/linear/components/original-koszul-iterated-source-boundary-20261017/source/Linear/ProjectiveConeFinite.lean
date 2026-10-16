module
public import Linear.HomogeneousMapFinite
public import Linear.ProjectiveCoordinateDomainMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- No base point and positive degree give the actual origin-only affine
zero locus of the original homogeneous tuple. -/
theorem HomogeneousEndomorphism.forms_zeroLocus
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) :
    MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range f.forms)) = {0} := by
  rw [MvPolynomial.zeroLocus_span]
  ext v
  constructor
  · intro hv
    have hz : f.evalVector v = 0 := by
      ext i
      exact hv (f.forms i) (Set.mem_range_self i)
    exact Set.mem_singleton_iff.mpr (by
      by_contra hv0
      exact f.noBasePoint v hv0 hz)
  · intro hv
    have hv0 : v = 0 := Set.mem_singleton_iff.mp hv
    subst v
    rintro p ⟨i, rfl⟩
    exact congrFun (f.evalVector_zero (Nat.ne_of_gt hq)) i

/-- The original homogeneous tuple induces a finite affine cone map.
No finite-map assumption is inserted. -/
theorem HomogeneousEndomorphism.polynomial_map_finite
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) :
    ((MvPolynomial.aeval f.forms : CoordinateRing n →ₐ[ℂ] CoordinateRing n).toRingHom).Finite := by
  exact homogeneous_polynomial_map_finite_of_origin_zeroLocus
    f.forms f.degree hq f.homogeneous (f.forms_zeroLocus hq)

/-- The actual induced homogeneous coordinate-domain action on the original
totally invariant variety is finite, stronger than a function-field statement. -/
theorem projectiveCoordinateDomainMap_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    (projectiveCoordinateDomainMap f V hq hf hV).toRingHom.Finite := by
  let π := Ideal.Quotient.mk V.ideal.toIdeal
  have hp : π.Finite := RingHom.Finite.of_surjective π Ideal.Quotient.mk_surjective
  have hc := hp.comp (f.polynomial_map_finite hq)
  have he : π.comp (MvPolynomial.aeval f.forms).toRingHom =
      (projectiveCoordinateDomainMap f V hq hf hV).toRingHom.comp π := by
    apply RingHom.ext
    intro p
    exact (projectiveCoordinateDomainMap_mk f V hq hf hV p).symm
  rw [he] at hc
  exact RingHom.Finite.of_comp_finite hc

end LinearStudy
