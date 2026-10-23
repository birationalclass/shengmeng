module
public import Linear.ProjectiveHomogeneousCoefficientTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace MvPolynomial
variable {R S : Type} [CommRing R] [CommRing S] {σ : Type}

/-- The inverse scalar map is derived from the original ring equivalence. -/
local instance projectiveCoefficientInverseForward (e : R ≃+* S) :
    RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e

/-- The reverse inverse scalar map is also derived,not an input. -/
local instance projectiveCoefficientInverseBackward (e : R ≃+* S) :
    RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e

/-- The ORIGINAL coefficient map of an actual coefficient ring equivalence
is invertible on every actual homogeneous polynomial piece. -/
def projectiveHomogeneousCoefficientEquiv (e : R ≃+* S) (m : ℕ) :
    homogeneousSubmodule σ R m ≃ₛₗ[e.toRingHom] homogeneousSubmodule σ S m where
  toFun := projectiveHomogeneousCoefficientMap e.toRingHom m
  invFun := projectiveHomogeneousCoefficientMap e.symm.toRingHom m
  left_inv p := by
    apply Subtype.ext
    exact MvPolynomial.map_leftInverse (f := e.symm.toRingHom) (g := e.toRingHom) e.symm_apply_apply p.1
  right_inv p := by
    apply Subtype.ext
    exact MvPolynomial.map_leftInverse (f := e.toRingHom) (g := e.symm.toRingHom) e.apply_symm_apply p.1
  map_add' p q := map_add (projectiveHomogeneousCoefficientMap e.toRingHom m) p q
  map_smul' r p := map_smulₛₗ (projectiveHomogeneousCoefficientMap e.toRingHom m) r p

/-- Its forward underlying map is the original polynomial coefficient map. -/
theorem projectiveHomogeneousCoefficientEquiv_apply (e : R ≃+* S) (m : ℕ)
    (p : homogeneousSubmodule σ R m) :
    projectiveHomogeneousCoefficientEquiv e m p =
      projectiveHomogeneousCoefficientMap e.toRingHom m p := rfl

/-- The inverse uses the inverse ORIGINAL coefficient ring equivalence. -/
theorem projectiveHomogeneousCoefficientEquiv_symm_apply (e : R ≃+* S) (m : ℕ)
    (p : homogeneousSubmodule σ S m) :
    (projectiveHomogeneousCoefficientEquiv e m).symm p =
      projectiveHomogeneousCoefficientMap e.symm.toRingHom m p := rfl

/-- The constructed homogeneous equivalence commutes with ORIGINAL
polynomial multiplication. This is the entry square needed for canonical
K versus Gamma(Spec K,O) coefficient alignment. -/
theorem projectiveHomogeneousCoefficientEquiv_multiply (e : R ≃+* S) (l m : ℕ)
    (p : homogeneousSubmodule σ R l) (q : homogeneousSubmodule σ R m) :
    projectiveHomogeneousCoefficientEquiv e (l+m) (projectiveHomogeneousMultiply l m p q) =
      projectiveHomogeneousMultiply l m (projectiveHomogeneousCoefficientEquiv e l p)
        (projectiveHomogeneousCoefficientEquiv e m q) := by
  apply Subtype.ext
  change MvPolynomial.map e.toRingHom (p.1*q.1) =
    MvPolynomial.map e.toRingHom p.1 * MvPolynomial.map e.toRingHom q.1
  exact map_mul (MvPolynomial.map (σ := σ) e.toRingHom) p.1 q.1

end MvPolynomial
