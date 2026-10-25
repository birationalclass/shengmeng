module
public import Linear.FiniteReducedFiberLocalFree
public import Linear.CoextensionResidueFiberPointProjector
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
/-- Derive the finite FREE input of the SAME ORIGINAL coextension fiber
trace from an ACTUAL reduced local fiber and pointwise LOCAL CM/dimension.
No global freeness/CM on original V is asserted. Geometric chart matching,
original Ext comparison and SAME top-H trace calibration remain OPEN. -/
theorem coextension_original_point_trace_one_of_reduced_local_fiber
    {R S K : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [Field K] [Algebra R S] [Algebra R K] [Module.Finite R S]
    [IsReduced (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))]
    [hCM : ∀ (P : Ideal S) [P.IsMaximal],IsCohenMacaulayLocalRing (Localization.AtPrime P)]
    (rs : List R) (hgen : Ideal.ofList rs=IsLocalRing.maximalIdeal R)
    (hlen : ∀ (P : Ideal S) [P.IsMaximal],
      (rs.length : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime P))
    (hres : Function.Surjective (algebraMap R K)) :
    letI : Module.Free R S := @finite_free_of_reduced_fiber_local_parameters R S _ _ _ _ _ _ _ hCM rs hgen hlen
    ∀ e : K ⊗[R] S,e ≠ 0 → e*e=e →
      ∃ m : K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))),
        coextensionOriginalResidueFiberPointEnd hres e m=m ∧
          coextensionOriginalFiberTrace (R:=R) (S:=S) (K:=K) m=1 := by
  letI : Module.Free R S := @finite_free_of_reduced_fiber_local_parameters R S _ _ _ _ _ _ _ hCM rs hgen hlen
  intro e he hi
  exact coextensionOriginalResidueFiberPointTrace_exists_one hres e he hi
end LinearStudy
