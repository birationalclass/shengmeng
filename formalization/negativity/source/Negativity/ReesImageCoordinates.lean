module

public import Negativity.ReesBaseChange
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open Polynomial
open scoped TensorProduct
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

def actualReesPolynomialMap (I : Ideal R) : S ⊗[R] reesAlgebra I →ₐ[S] S[X] :=
  (reesAlgebra (I.map (algebraMap R S))).val.comp (actualReesBaseChangeMap I)

theorem actual_rees_polynomial_kernel (I : Ideal R) :
    RingHom.ker (actualReesPolynomialMap (S := S) I).toRingHom =
      RingHom.ker (actualReesBaseChangeMap (S := S) I).toRingHom := by
  ext p
  change (actualReesBaseChangeMap I p).1 = 0 ↔ actualReesBaseChangeMap I p = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

def actualReesImageCoordinates (I : Ideal R) :
    ((S ⊗[R] reesAlgebra I) ⧸ RingHom.ker (actualReesPolynomialMap (S := S) I).toRingHom)
      ≃ₐ[S] reesAlgebra (I.map (algebraMap R S)) :=
  (Ideal.quotientEquivAlgOfEq S (actual_rees_polynomial_kernel I)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (actual_rees_base_change_surjective I))

/-- Final theorem: the genuine affine image algebra of the polynomial
map is the Rees algebra of the extended ideal. The quotient map sends
each tensor a ⊗ p to the polynomial a·p with coefficients pulled back
along R→S. This is an explicit coordinate identification, with no
flatness or finite-generation hypothesis. -/
theorem actual_rees_image_coordinates_on_tensors (I : Ideal R) (s : S) (p : reesAlgebra I) :
    (actualReesImageCoordinates I
      (Ideal.Quotient.mk _ (s ⊗ₜ[R] p))).1 = s • p.1.map (algebraMap R S) := by
  simp only [actualReesImageCoordinates, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

end
end Negativity
