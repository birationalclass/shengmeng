module
public import Linear.OriginalDegreeVeroneseCoefficientAmbientRestriction
public import Linear.OriginalDegreeVeroneseCoefficientChartEquiv
public import Linear.OriginalDegreeVeroneseCoefficientLocalizationOverlap
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
local instance originalDegreeVeroneseCoefficientRestrictionSquareGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- The two native weighted module restrictions commute with the exact
chart equivalence on the same product chart. -/
theorem originalDegreeVeroneseCoefficientRestriction_square
    {d e : ℕ} {f g : V} (hf : f ∈ P d) (hg : g ∈ P e) (k : ℤ)
    (x : originalDegreeVeroneseCoefficientRegradedChart B D hD q d f k) :
    originalDegreeVeroneseCoefficientChartEquiv B D hD q
        (SetLike.mul_mem_graded hf hg) k
        (originalDegreeVeroneseCoefficientRegradedRestriction B D hD q hf hg k x) =
      originalDegreeVeroneseCoefficientAmbientRestriction B D hD q hf hg k
        (originalDegreeVeroneseCoefficientChartEquiv B D hD q hf k x) := by
  exact Subtype.ext
    (originalDegreeVeroneseCoefficientLocalization_overlap B D hD q f g x.val)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientRestriction_square
#print axioms LinearStudy.originalDegreeVeroneseCoefficientRestriction_square

