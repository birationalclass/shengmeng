module
public import Linear.OriginalDegreeVeroneseChartRingEquivMk
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
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeroneseProductChartGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

/-- The Veronese restriction on a product chart, with all indices fixed. -/
def originalDegreeVeroneseChartRestrict
    {e : ℕ} (f g : V) (hg : g ∈ P e) :
    Away P f →+* Away P (f * g) :=
  awayMap P (f := f) (g := g) (x := f * g) hg rfl

/-- The original restriction on the corresponding product chart. -/
def originalDegreeVeroneseAmbientChartRestrict
    {e : ℕ} (f g : V) (hg : g ∈ P e) :
    Away B (f : S) →+* Away B ((f * g : V) : S) :=
  awayMap B (f := (f : S)) (g := (g : S))
    (x := ((f * g : V) : S)) (show (g : S) ∈ B (q * e) from hg) rfl

theorem originalDegreeVeroneseChartRestrict_mk
    {d e : ℕ} {f g : V} (hf : f ∈ P d) (hg : g ∈ P e)
    (n : ℕ) (a : V) (ha : a ∈ P (n • d)) :
    originalDegreeVeroneseChartRestrict B q f g hg (Away.mk P hf n a ha) =
      Away.mk P (SetLike.mul_mem_graded hf hg) n (a * g ^ n) (by
        rw [smul_add]
        exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n hg)) :=
  awayMap_mk P (f := f) (g := g) (x := f * g) hg rfl n hf a ha

omit hq in
theorem originalDegreeVeroneseAmbientChartRestrict_mk
    {d e : ℕ} {f g : V} (hg : g ∈ P e)
    (hfS : (f : S) ∈ B d) (n : ℕ) (a : S) (haS : a ∈ B (n • d)) :
    originalDegreeVeroneseAmbientChartRestrict B q f g hg (Away.mk B hfS n a haS) =
      Away.mk B (SetLike.mul_mem_graded hfS (show (g : S) ∈ B (q * e) from hg))
        n (a * (g : S) ^ n) (by
          rw [smul_add]
          exact SetLike.mul_mem_graded haS
            (SetLike.pow_mem_graded n (show (g : S) ∈ B (q * e) from hg))) :=
  awayMap_mk B (f := (f : S)) (g := (g : S)) (x := ((f * g : V) : S))
    (show (g : S) ∈ B (q * e) from hg) rfl n hfS a haS

end LinearStudy
#check LinearStudy.originalDegreeVeroneseChartRestrict
#print axioms LinearStudy.originalDegreeVeroneseChartRestrict
#check LinearStudy.originalDegreeVeroneseAmbientChartRestrict
#print axioms LinearStudy.originalDegreeVeroneseAmbientChartRestrict
#check LinearStudy.originalDegreeVeroneseChartRestrict_mk
#print axioms LinearStudy.originalDegreeVeroneseChartRestrict_mk
#check LinearStudy.originalDegreeVeroneseAmbientChartRestrict_mk
#print axioms LinearStudy.originalDegreeVeroneseAmbientChartRestrict_mk

