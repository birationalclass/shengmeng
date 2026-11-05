module
public import Linear.OriginalDegreeVeroneseGrading
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open HomogeneousLocalization
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local instance : GradedAlgebra (originalDegreeVeronesePiece B q) :=
  originalDegreeVeroneseGrading B q hq.out

/-- On a regraded chart, compare the degree-zero fractions in the
original ordinary localization. -/
def originalDegreeVeroneseChartValue
    (f : originalDegreeVeroneseAlgebra B q) :
    Away (originalDegreeVeronesePiece B q) f →+* Localization.Away (f : S) :=
  (Localization.awayMap (originalDegreeVeroneseAlgebra B q).val.toRingHom f).comp
    (algebraMap _ _)

theorem originalDegreeVeroneseChartValue_mk
    {d : ℕ} {f : originalDegreeVeroneseAlgebra B q}
    (hf : f ∈ originalDegreeVeronesePiece B q d)
    (n : ℕ) {a : originalDegreeVeroneseAlgebra B q}
    (ha : a ∈ originalDegreeVeronesePiece B q (n • d))
    (hfS : (f : S) ∈ B (q * d)) (haS : (a : S) ∈ B (n • (q * d))) :
    originalDegreeVeroneseChartValue B q f
      (Away.mk (originalDegreeVeronesePiece B q) hf n a ha) =
      (Away.mk B hfS n (a : S) haS).val := by
  change Localization.awayMap (originalDegreeVeroneseAlgebra B q).val.toRingHom f
    (Away.mk (originalDegreeVeronesePiece B q) hf n a ha).val =
      (Away.mk B hfS n (a : S) haS).val
  rw [Away.val_mk, Away.val_mk]
  simp only [Localization.awayMap, IsLocalization.Away.map, Localization.mk_eq_mk']
  rw [IsLocalization.map_mk']
  congr 1

end LinearStudy
#check LinearStudy.originalDegreeVeroneseChartValue
#print axioms LinearStudy.originalDegreeVeroneseChartValue
#check LinearStudy.originalDegreeVeroneseChartValue_mk
#print axioms LinearStudy.originalDegreeVeroneseChartValue_mk
