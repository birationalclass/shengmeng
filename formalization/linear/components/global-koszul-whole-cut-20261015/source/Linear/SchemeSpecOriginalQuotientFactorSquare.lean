module
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {R T : Type u} [CommRing R] [CommRing T]

/-- An actual quotient isomorphism compatible with the ORIGINAL ring
map induces a scheme isomorphism OVER the original ambient spectrum.
Compatibility with the original ring map is an explicit input here. -/
theorem schemeSpec_originalQuotientFactor_square (I : Ideal R)
    (e : (R ⧸ I) ≃+* T) (u : R →+* T)
    (hu : ∀ x,e (Ideal.Quotient.mk I x) = u x) :
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom u) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  have he : e.symm.toRingHom.comp u = Ideal.Quotient.mk I := by
    ext x
    change e.symm (u x) = Ideal.Quotient.mk I x
    rw [← hu x]
    exact e.symm_apply_apply _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp u)) = _
  rw [he]

end LinearStudy