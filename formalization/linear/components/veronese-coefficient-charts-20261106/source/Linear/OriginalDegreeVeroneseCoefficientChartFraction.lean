module
public import Linear.OriginalDegreeVeroneseCoefficientRegradedChart
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
local instance originalDegreeVeroneseCoefficientChartFractionGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- Homogeneous action on the actual shifted Veronese grading. -/
def originalDegreeVeroneseCoefficientShiftedAction (k : ℤ) :=
  @integerGradingShift_smul_homogeneous K V W
    (inferInstanceAs (Field K)) (inferInstanceAs (CommRing V))
    (inferInstanceAs (Algebra K V)) (inferInstanceAs (AddCommGroup W))
    (Submodule.module' W) (Submodule.module W)
    P (originalDegreeVeroneseCoefficientChartFractionGraded B q) E
    (originalDegreeVeroneseCoefficient_smul_homogeneous B D hD q) k

/-- The native single-fraction theorem at the shifted regraded coefficients. -/
def originalDegreeVeroneseCoefficientRegradedChart_exists_fraction (k : ℤ) :=
  @nativeGradedModuleAwayDegreeZero_exists_fraction K V W
    (inferInstanceAs (Field K)) (inferInstanceAs (CommRing V))
    (inferInstanceAs (Algebra K V)) (inferInstanceAs (AddCommGroup W))
    (Submodule.module W) (Submodule.module' W)
    P (originalDegreeVeroneseCoefficientChartFractionGraded B q)
    (integerGradingShift E k)
    (originalDegreeVeroneseCoefficientShiftedAction B D hD q k)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientShiftedAction
#print axioms LinearStudy.originalDegreeVeroneseCoefficientShiftedAction
#check LinearStudy.originalDegreeVeroneseCoefficientRegradedChart_exists_fraction
#print axioms LinearStudy.originalDegreeVeroneseCoefficientRegradedChart_exists_fraction

