module
public import Linear.OriginalDegreeVeronesePrimeDenominator
public import Linear.OriginalDegreeVeronesePromotedFraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u v w
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeronesePrimeLocalizationGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "F" => originalDegreeVeroneseProjHom B q

local notation "Q" => originalDegreeVeroneseRegradedPrimeCompl B q
local notation "T" => originalDegreeVeroneseAmbientPrimeCompl B

variable {M : Type w} [AddCommGroup M] [Module K M] [Module S M]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ a : M, a ∈ D d → c • a ∈ D ((n : ℤ) + d))
local notation "W" => originalDegreeVeroneseCoefficient B D hD q

/-- Send a fraction at the contracted prime to its actual original value. -/
def originalDegreeVeronesePrimeLocalization (x : Proj B)
    (z : LocalizedModule (Q x) W) : LocalizedModule (T x) M :=
  @LocalizedModule.liftOn V (inferInstanceAs (CommSemiring V)) (Q x) W
    (inferInstanceAs (AddCommMonoid W)) (Submodule.module W) (LocalizedModule (T x) M) z
    (fun p : W × Q x => LocalizedModule.mk (p.1 : M)
      (originalDegreeVeronesePrimeDenominator B q x p.2))
    (by
      intro p p' h
      change LocalizedModule.r (Q x) W p p' at h
      obtain ⟨t, ht⟩ := h
      exact LocalizedModule.mk_eq.mpr
        ⟨originalDegreeVeronesePrimeDenominator B q x t,
          congrArg (fun z : W => (z : M)) ht⟩)

theorem originalDegreeVeronesePrimeLocalization_mk (x : Proj B)
    (a : W) (s : Q x) :
    originalDegreeVeronesePrimeLocalization B q D hD x (LocalizedModule.mk a s) =
      LocalizedModule.mk (a : M) (originalDegreeVeronesePrimeDenominator B q x s) := rfl

end LinearStudy
#check LinearStudy.originalDegreeVeronesePrimeLocalization
#print axioms LinearStudy.originalDegreeVeronesePrimeLocalization
#check LinearStudy.originalDegreeVeronesePrimeLocalization_mk
#print axioms LinearStudy.originalDegreeVeronesePrimeLocalization_mk

