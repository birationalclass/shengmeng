module
public import Linear.OriginalDegreeVeroneseChartRefinement
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
local instance originalDegreeVeroneseChartMapSquareGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

/-- The degree-zero comparison commutes as ring homomorphisms with
each map to a chart indexed by a product. -/
theorem originalDegreeVeroneseChartRingHomSquare
    {d e : ℕ} {f g x : V} (hf : f ∈ P d) (hg : g ∈ P e)
    (hx : x = f * g) (hxS : (x : S) = (f : S) * (g : S))
    (hxP : x ∈ P (d + e)) :
    (originalDegreeVeroneseChartRingEquiv B q hxP).toRingHom.comp
      (awayMap P (f := f) (g := g) (x := x) hg hx) =
    (awayMap B (f := (f : S)) (g := (g : S)) (x := (x : S))
      (show (g : S) ∈ B (q * e) from hg) hxS).comp
      (originalDegreeVeroneseChartRingEquiv B q hf).toRingHom := by
  subst x
  apply RingHom.ext
  intro z
  exact originalDegreeVeroneseChartRingEquiv_awayMap B q hf hg z

end LinearStudy
#check LinearStudy.originalDegreeVeroneseChartRingHomSquare
#print axioms LinearStudy.originalDegreeVeroneseChartRingHomSquare

