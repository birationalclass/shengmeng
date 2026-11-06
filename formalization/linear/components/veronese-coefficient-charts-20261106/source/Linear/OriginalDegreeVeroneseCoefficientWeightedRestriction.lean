module
public import Linear.OriginalDegreeVeroneseCoefficientChartImage
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
local instance originalDegreeVeroneseCoefficientWeightedOverlapGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- The actual regraded module restriction on a product chart, including the
same integer shift on both the source and target. -/
def originalDegreeVeroneseCoefficientRegradedRestriction
    {d e : ℕ} {f g : V} (hf : f ∈ P d) (hg : g ∈ P e) (k : ℤ) :=
  @nativeGradedModuleWeightedOverlapMap K V W
    (inferInstanceAs (Field K)) (inferInstanceAs (CommRing V))
    (inferInstanceAs (Algebra K V)) (inferInstanceAs (AddCommGroup W))
    (Submodule.module W) (Submodule.module' W)
    P (originalDegreeVeroneseCoefficientWeightedOverlapGraded B q)
    (integerGradingShift E k)
    (originalDegreeVeroneseCoefficientShiftedAction B D hD q k)
    d e f g hf hg

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientRegradedRestriction
#print axioms LinearStudy.originalDegreeVeroneseCoefficientRegradedRestriction

