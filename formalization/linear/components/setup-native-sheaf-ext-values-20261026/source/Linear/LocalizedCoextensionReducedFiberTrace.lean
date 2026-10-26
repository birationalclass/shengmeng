module
public import Linear.LocalizedCoextensionFiberPointTrace
public import Linear.FiniteReducedFiberLocalFree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
variable {R S Q K : Type u} [CommRing R] [CommRing S] [CommRing Q]
variable [Field K] [Algebra R S] [Algebra R Q] [Algebra R K] [Algebra Q K]
variable [IsScalarTower R Q K] [Module.Finite R S]
variable (P : Submonoid R) [IsLocalization P Q] [IsLocalRing Q] [IsNoetherianRing Q]
/-- Derive freeness of the ACTUAL localized original source from its
ACTUAL reduced closed fiber and pointwise LOCAL CM/dimension data.
No generic-open replacement or global S/R free/flat input. -/
theorem localized_finite_source_free_of_reduced_fiber
    (rs : List Q) (hgen : Ideal.ofList rs=IsLocalRing.maximalIdeal Q)
    (hlocal : let S' := LocalizedModule P S
      letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
      letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=P) Q
      IsReduced (S' ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q S')) ∧
        ∀ (p : Ideal S') (_ : p.IsMaximal),
          IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
            (rs.length : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p)) :
    letI : Module Q (LocalizedModule P S) := LocalizedModule.moduleOfIsLocalization
    Module.Free Q (LocalizedModule P S) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=P) Q
  letI : Module.Finite Q S' := Module.Finite.of_isLocalizedModule P (Rₚ:=Q)
    (LocalizedModule.mkLinearMap P S)
  letI : IsReduced (S' ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q S')) := hlocal.1
  let hCM : ∀ (p : Ideal S') [p.IsMaximal],
      IsCohenMacaulayLocalRing (Localization.AtPrime p) := fun p hp => (hlocal.2 p hp).1
  have hdim : ∀ (p : Ideal S') [p.IsMaximal],
      (rs.length : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p) :=
    fun p hp => (hlocal.2 p hp).2
  exact @finite_free_of_reduced_fiber_local_parameters Q S' _ _ _ _ _ _ _ hCM rs hgen hdim
/-- SAME ORIGINAL coefficient fiber,SAME ORIGINAL source point projector,
and LITERAL original eval1 base change. Local freeness is DERIVED from the
actual reduced local fiber data,never assumed globally. Original geometric
chart instantiation,Ext comparison and SAME top-H trace calibration remain OPEN. -/
theorem original_coextension_point_trace_one_of_local_reduced_fiber
    (rs : List Q) (hgen : Ideal.ofList rs=IsLocalRing.maximalIdeal Q)
    (hlocal : let S' := LocalizedModule P S
      letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
      letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=P) Q
      IsReduced (S' ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q S')) ∧
        ∀ (p : Ideal S') (_ : p.IsMaximal),
          IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
            (rs.length : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p))
    (hinj : Function.Injective (algebraMap R Q))
    (hres : Function.Surjective (algebraMap R K))
    (e : K ⊗[R] S) (he : e ≠ 0) (hi : e*e=e) :
    ∃ m : K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))),
      coextensionOriginalResidueFiberPointEnd hres e m=m ∧
        coextensionOriginalBaseChangedEvaluationAtOne (R:=R) (S:=S) (K:=K) m=1 := by
  have hfree := localized_finite_source_free_of_reduced_fiber (S:=S) P rs hgen hlocal
  exact localizedCoextensionOriginalResidueFiberPointTrace_exists_one P hfree hinj hres e he hi
end LinearStudy
