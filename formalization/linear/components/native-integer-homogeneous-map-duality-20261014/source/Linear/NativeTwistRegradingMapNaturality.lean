module
public import Linear.NativeProjectiveTwistRegrading
public import Linear.NativeProjectiveDegreeZeroMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S M E : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup E] [Module K E] [Module S E]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) (D' : ℤ → Submodule K E)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ B n →
  ∀ x : M, x ∈ D d → b • x ∈ D ((n:ℤ)+d))
variable (hD' : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ B n →
  ∀ x : E, x ∈ D' d → b • x ∈ D' ((n:ℤ)+d))
variable (e : M →ₗ[S] E)
variable (he : ∀ d : ℤ, ∀ x : M, x ∈ D d → e x ∈ D' d)

/-- The EXISTING actual native regrading isomorphism respects EVERY
ORIGINAL degree-zero module map on every original open and prime. Uses
actual identity on localized values,not an assumed twist map square.
This is primal SHEAF-map compatibility;Cech/Hom duality-map and original
Koszul connecting compatibility remain separate. -/
theorem nativeProjectiveTwistRegradingIso_map (k : ℤ) :
    (nativeProjectiveTwistRegradingIso B D hD k).inv ≫
      nativeProjectiveDegreeZeroSheafMap B (integerGradingShift D k) (integerGradingShift D' k)
        (integerGradingShift_smul_homogeneous B D hD k)
        (integerGradingShift_smul_homogeneous B D' hD' k) e
        (fun d x hx => he (d+k) x hx) 0 ≫
      (nativeProjectiveTwistRegradingIso B D' hD' k).hom =
    nativeProjectiveDegreeZeroSheafMap B D D' hD hD' e he k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

end LinearStudy
