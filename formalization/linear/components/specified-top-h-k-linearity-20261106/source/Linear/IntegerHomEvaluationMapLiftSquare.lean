module
public import Linear.IntegerGradedHomEvaluationCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J M N : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup N] [Module K N] [Module S N]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (w : I → ℤ) (v : J → ℤ)
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (βM : (I → S) →ₗ[S] M) (βN : (J → S) →ₗ[S] N)
variable (hβM : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B w t → βM x ∈ D t)
variable (hβN : ∀ t : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece B v t → βN x ∈ E t)
variable (e : M →ₗ[S] N)
variable (he : ∀ t : ℤ, ∀ x : M, x ∈ D t → e x ∈ E t)
variable (τ : (I → S) →ₗ[S] (J → S))
variable (hτ : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B w t →
  τ x ∈ integerShiftedFreePiece B v t)
variable (hsquare : βN.comp τ=e.comp βM)
include hsquare

/-- The ORIGINAL coefficient square follows from an ORDINARY original
module lift betaN o tau=e o betaM. It keeps phi(e(betaM(e_i))) and the
actual original matrix tau(e_i)_j. No cohomology/duality identity assumed.
The actual lift is constructed separately from ordinary graded onto betaN. -/
theorem integerHomEvaluationCoordinates_map_lift (d : ℤ) :
    (integerGradedHomEvaluationCoordinates B w D βM hβM d).comp
      (integerGradedHomPrecomposition B D E e he d) =
    (integerShiftedFreeDualDegreeRelationMatrix τ B w v hτ d).comp
      (integerGradedHomEvaluationCoordinates B v E βN hβN d) := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext i
  change φ.1 (e (βM (Pi.single i (1:S)))) =
    ∑ j, τ (Pi.single i (1:S)) j * φ.1 (βN (Pi.single j (1:S)))
  have hmap := LinearMap.congr_fun hsquare (Pi.single i (1:S))
  simp only [LinearMap.comp_apply] at hmap
  rw [← hmap]
  simpa only [LinearMap.pi_apply,integerShiftedFreeMapEntry,LinearMap.comp_apply]
    using integerShiftedFreeMap_apply (LinearMap.pi (fun _ : Unit => φ.1.comp βN))
      (τ (Pi.single i (1:S))) ()

end LinearStudy
