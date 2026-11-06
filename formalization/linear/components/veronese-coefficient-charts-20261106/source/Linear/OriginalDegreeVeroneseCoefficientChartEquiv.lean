module
public import Linear.OriginalDegreeVeroneseCoefficientChartImage
public import Mathlib.Logic.Equiv.Set
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
/-- The native weighted charts on the two coefficient modules have the same
elements under the fraction-value correspondence. -/
def originalDegreeVeroneseCoefficientChartEquiv
    {d : ℕ} {f : V} (hf : f ∈ P d) (k : ℤ) :=
  (Equiv.Set.image
    (originalDegreeVeroneseCoefficientLocalization B D hD q f)
    (originalDegreeVeroneseCoefficientRegradedChart B D hD q d f k : Set _)
    (originalDegreeVeroneseCoefficientLocalization_injective B D hD q f)).trans
    (Set.equivOfEq (originalDegreeVeroneseCoefficientChartImage B D hD q hf k))

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientChartEquiv
#print axioms LinearStudy.originalDegreeVeroneseCoefficientChartEquiv

