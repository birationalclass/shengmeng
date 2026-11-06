module
public import Linear.OriginalDegreeVeroneseCoefficientLocalization
public import Linear.IntegerGradingShift
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
variable (q : ℕ)
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "P" => originalDegreeVeronesePiece B q
local notation "W" => originalDegreeVeroneseCoefficient B D hD q
local notation "E" => originalDegreeVeroneseCoefficientPiece B D hD q
/-- Numerators at the two actual chart degrees have the same values. -/
theorem originalDegreeVeroneseCoefficientNumerator_image (d n : ℕ) (k : ℤ) :
    (fun a : W => (a : M)) '' (integerGradingShift E k ((n*d : ℕ) : ℤ) : Set W) =
      (integerGradingShift D ((q : ℤ)*k) ((n*(q*d) : ℕ) : ℤ) : Set M) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    apply (originalDegreeVeroneseChartNumerator_mem_iff B D hD q d n k a).mp
    change a ∈ E (((n*d : ℕ) : ℤ) + k) at ha
    simpa only [Nat.cast_mul] using ha
  · intro a ha
    obtain ⟨b, hba, hb⟩ := originalDegreeVeroneseChartNumerator_exists B D hD q d n k a ha
    refine ⟨b, ?_, hba⟩
    change b ∈ E (((n*d : ℕ) : ℤ) + k)
    simpa only [Nat.cast_mul] using hb

omit [IsScalarTower K S M] in
theorem originalDegreeVeroneseCoefficientLocalization_mk_pow (f : V) (n : ℕ) (a : W) :
    originalDegreeVeroneseCoefficientLocalization B D hD q f
        (LocalizedModule.mk a (⟨f^n, ⟨n,rfl⟩⟩ : Submonoid.powers f)) =
      LocalizedModule.mk (a : M) (⟨(f : S)^n, ⟨n,rfl⟩⟩ : Submonoid.powers (f : S)) := rfl

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientNumerator_image
#print axioms LinearStudy.originalDegreeVeroneseCoefficientNumerator_image
#check LinearStudy.originalDegreeVeroneseCoefficientLocalization_mk_pow
#print axioms LinearStudy.originalDegreeVeroneseCoefficientLocalization_mk_pow

