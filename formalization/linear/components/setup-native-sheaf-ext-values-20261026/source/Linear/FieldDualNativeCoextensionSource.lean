module
public import Linear.CoextensionFractionFunctional
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory
universe u
variable {K B Q N : Type u} [Field K] [CommRing B] [CommRing Q] [Algebra K Q]
variable [AddCommGroup N] [Module K N] [Module B N]
/-- A field-linear duality which PROVABLY retains the ORIGINAL B action
is an ACTUAL B-linear equivalence to the native coextension on Q,with
scalars restricted through the ORIGINAL beta. No module action is defined
by transport through E. -/
def fieldDualNativeCoextensionSourceEquiv (beta : B →+* Q)
    (E : N ≃ₗ[K] Module.Dual K Q)
    (hE : ∀ (b : B) (z : N) (q : Q),E (b • z) q=E z (q*beta b)) :
    N ≃ₗ[B] (ModuleCat.restrictScalars beta).obj
      ((ModuleCat.coextendScalars (algebraMap K Q)).obj (ModuleCat.of K K)) := by
  let c := coextensionOriginalDualEquiv (R:=K) (S:=Q)
  let e : N ≃+ (ModuleCat.restrictScalars beta).obj
      ((ModuleCat.coextendScalars (algebraMap K Q)).obj (ModuleCat.of K K)) :=
    E.toAddEquiv.trans c.symm.toAddEquiv
  refine { e with map_smul' := ?_ }
  intro b z
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro q
  change E (b • z) (show Q from q)=E z ((show Q from q)*beta b)
  exact hE b z q
/-- The native-source-linear equivalence retains EVERY original functional
value,not merely the existence of an unspecified object isomorphism. -/
theorem fieldDualNativeCoextensionSourceEquiv_apply (beta : B →+* Q)
    (E : N ≃ₗ[K] Module.Dual K Q)
    (hE : ∀ (b : B) (z : N) (q : Q),E (b • z) q=E z (q*beta b))
    (z : N) (q : Q) :
    (show (ModuleCat.coextendScalars (algebraMap K Q)).obj (ModuleCat.of K K) from
      fieldDualNativeCoextensionSourceEquiv beta E hE z) q=E z q := by
  rfl
end LinearStudy
