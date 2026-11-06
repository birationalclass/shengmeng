module
public import Linear.OriginalDegreeVeroneseCoefficientWeightedRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u
variable {K S M : Type u}
variable [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ x : M, x ∈ D d → c • x ∈ D ((n : ℤ) + d))
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "P" => originalDegreeVeronesePiece B q
local notation "W" => originalDegreeVeroneseCoefficient B D hD q
local notation "E" => originalDegreeVeroneseCoefficientPiece B D hD q
local instance originalDegreeVeroneseCoefficientAmbientOverlapGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- The native original restriction in the same product chart, written
with original degree q*(d+e) and integer shift q*k. -/
def originalDegreeVeroneseCoefficientAmbientRestriction
    {d e : ℕ} {f g : V} (hf : f ∈ P d) (hg : g ∈ P e) (k : ℤ)
    (x : originalDegreeVeroneseAmbientCoefficientChart B D q d f k) :
    originalDegreeVeroneseAmbientCoefficientChart B D q (d+e) (f*g) k := by
  have hfS : (f : S) ∈ B (q*d) := hf
  have hgS : (g : S) ∈ B (q*e) := hg
  refine ⟨originalLocalizedModuleAwayOverlap (f : S) (g : S) x.val, ?_⟩
  have hx := nativeGradedModuleWeightedOverlap_mem B
    (integerGradingShift D ((q : ℤ)*k))
    (integerGradingShift_smul_homogeneous B D hD ((q : ℤ)*k))
    (q*d) (q*e) (f : S) (g : S) hfS hgS x.val x.property
  change _ ∈ nativeGradedModuleAwayDegreeZero B
    (integerGradingShift D ((q : ℤ)*k)) (q*(d+e)) ((f : S)*(g : S))
  simpa only [Nat.mul_add] using hx

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientAmbientRestriction
#print axioms LinearStudy.originalDegreeVeroneseCoefficientAmbientRestriction

