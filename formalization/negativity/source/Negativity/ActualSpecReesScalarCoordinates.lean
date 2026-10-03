module
public import Negativity.ReesRingEquivReuse
public import Negativity.ActualSpecIdealPullback

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

def actualSpecReesScalarEquiv {R : Type u} [CommRing R] (I : Ideal R) :
    reesAlgebra I ≃+*
      reesAlgebra ((actualSpecIdealSheaf I).ideal ⟨⊤, isAffineOpen_top _⟩) where
  toFun p := ⟨p.1.map (Scheme.ΓSpecIso (.of R)).inv.hom, by
    intro n
    rw [actual_spec_ideal_sheaf_top, Polynomial.coeff_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (p.2 n)⟩
  invFun p := ⟨p.1.map (Scheme.ΓSpecIso (.of R)).hom.hom, by
    intro n
    rw [Polynomial.coeff_map]
    have hp : p.1.coeff n ∈ (I.map (Scheme.ΓSpecIso (.of R)).inv.hom) ^ n := by
      simpa only [actual_spec_ideal_sheaf_top] using p.2 n
    rw [← Ideal.map_pow] at hp
    exact (Ideal.symm_apply_mem_of_equiv_iff
      (f := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv)).mpr hp⟩
  left_inv p := by
    apply Subtype.ext
    change (Polynomial.mapEquiv (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv).symm
      ((Polynomial.mapEquiv (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv) p.1) = _
    exact (Polynomial.mapEquiv _).symm_apply_apply p.1
  right_inv p := by
    apply Subtype.ext
    change (Polynomial.mapEquiv (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv)
      ((Polynomial.mapEquiv (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv).symm p.1) = _
    exact (Polynomial.mapEquiv _).apply_symm_apply p.1
  map_mul' p q := Subtype.ext (Polynomial.map_mul _)
  map_add' p q := Subtype.ext (Polynomial.map_add _)

@[simp]
theorem actualSpecReesScalarEquiv_coeff {R : Type u} [CommRing R]
    (I : Ideal R) (p : reesAlgebra I) (n : ℕ) :
    (actualSpecReesScalarEquiv I p).1.coeff n =
      (Scheme.ΓSpecIso (.of R)).inv (p.1.coeff n) :=
  Polynomial.coeff_map _ n

@[simp]
theorem actualSpecReesScalarEquiv_monomial {R : Type u} [CommRing R]
    (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    actualSpecReesScalarEquiv I (actualReesPowerMonomial I n r) =
      actualReesPowerMonomial ((actualSpecIdealSheaf I).ideal ⟨⊤, isAffineOpen_top _⟩) n
        ⟨(Scheme.ΓSpecIso (.of R)).inv r.1, by
          rw [actual_spec_ideal_sheaf_top, ← Ideal.map_pow]
          exact Ideal.mem_map_of_mem _ r.2⟩ := by
  apply Subtype.ext
  exact Polynomial.map_monomial _

/-- The scalar ring of native W cohomology and the canonical scalar ring
of the ideal-power class module are linked by genuine affine coordinates. -/
def actualReesCechScalarEquiv {R : Type u} [CommRing R] (I : Ideal R) :
    Γ(Spec (.of (reesAlgebra I)), ⊤) ≃+*
      reesAlgebra ((actualSpecIdealSheaf I).ideal ⟨⊤, isAffineOpen_top _⟩) :=
  (Scheme.ΓSpecIso (.of (reesAlgebra I))).commRingCatIsoToRingEquiv.trans
    (actualSpecReesScalarEquiv I)

/-- Restricting a genuine module through an actual ring isomorphism
preserves finite generation. This is the semilinear identity map,
whose scalar map is proved surjective. -/
theorem actual_ring_equiv_restricted_module_finite_iff
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (e : R ≃+* S) (M : Type w) [AddCommMonoid M] [Module S M] :
    letI : Module R M := Module.compHom M e.toRingHom
    Module.Finite R M ↔ Module.Finite S M := by
  letI : Module R M := Module.compHom M e.toRingHom
  let q : M →ₛₗ[e.toRingHom] M :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  exact LinearMap.finite_iff_of_bijective q Function.bijective_id

#print axioms actualSpecReesScalarEquiv
#print axioms actualReesCechScalarEquiv
#print axioms actual_ring_equiv_restricted_module_finite_iff
end
end Negativity
