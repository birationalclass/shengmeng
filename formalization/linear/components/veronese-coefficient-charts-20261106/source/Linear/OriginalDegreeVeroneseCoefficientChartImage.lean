module
public import Linear.OriginalDegreeVeroneseCoefficientChartFraction
public import Linear.NativeGradedWeightedChartImage
public import Linear.OriginalDegreeVeroneseCoefficientFractionValues
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
local instance originalDegreeVeroneseCoefficientNativeImageGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- The actual original weighted chart at the same denominator and shift q*k. -/
abbrev originalDegreeVeroneseAmbientCoefficientChart (d : ℕ) (f : V) (k : ℤ) :=
  nativeGradedModuleAwayDegreeZero (K := K) (R := S) (M := M)
    B (integerGradingShift D ((q : ℤ) * k)) (q*d) (f : S)

/-- The fraction inclusion carries the native regraded weighted chart onto
the native original weighted chart, for an arbitrary integer shift k. -/
def originalDegreeVeroneseCoefficientChartImage
    {d : ℕ} {f : V} (hf : f ∈ P d) (k : ℤ) :=
  @nativeGradedWeightedChart_image K V S W M
    (inferInstanceAs (Field K)) (inferInstanceAs (CommRing V)) (inferInstanceAs (CommRing S))
    (inferInstanceAs (Algebra K V)) (inferInstanceAs (Algebra K S))
    (inferInstanceAs (AddCommGroup W)) (inferInstanceAs (AddCommGroup M))
    (Submodule.module' W) (inferInstanceAs (Module K M))
    (Submodule.module W) (inferInstanceAs (Module S M))
    P B (originalDegreeVeroneseCoefficientNativeImageGraded B q) (inferInstanceAs (GradedAlgebra B))
    (integerGradingShift E k) (integerGradingShift D ((q : ℤ)*k))
    (originalDegreeVeroneseCoefficientShiftedAction B D hD q k)
    (integerGradingShift_smul_homogeneous B D hD ((q : ℤ)*k))
    d (q*d) f (f : S) hf (show (f : S) ∈ B (q*d) from hf)
    (fun a : W => (a : M)) (fun n => originalDegreeVeroneseCoefficientNumerator_image B D hD q d n k)
    (originalDegreeVeroneseCoefficientLocalization B D hD q f)
    (originalDegreeVeroneseCoefficientLocalization_mk_pow B D hD q f)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseAmbientCoefficientChart
#print axioms LinearStudy.originalDegreeVeroneseAmbientCoefficientChart
#check LinearStudy.originalDegreeVeroneseCoefficientChartImage
#print axioms LinearStudy.originalDegreeVeroneseCoefficientChartImage

