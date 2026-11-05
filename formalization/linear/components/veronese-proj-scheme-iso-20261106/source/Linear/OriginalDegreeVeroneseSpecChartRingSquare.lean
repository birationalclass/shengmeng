module
public import Linear.OriginalDegreeVeroneseChartMapSquare
public import Mathlib.Algebra.Category.Ring.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open HomogeneousLocalization CategoryTheory
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeroneseChartCommRingGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

/-- The bundled regraded chart ring at f. -/
def originalDegreeVeroneseBundledChart (f : V) : CommRingCat.{v} :=
  CommRingCat.of (Away P f)

/-- The bundled original chart ring at the image of f. -/
def originalDegreeVeroneseBundledAmbientChart (f : V) : CommRingCat.{v} :=
  CommRingCat.of (Away B (f : S))

local notation "VC" => originalDegreeVeroneseBundledChart B q
local notation "SC" => originalDegreeVeroneseBundledAmbientChart B q

def originalDegreeVeroneseBundledChartIso
    {d : ℕ} {f : V} (hf : f ∈ P d) : VC f ≅ SC f :=
  (originalDegreeVeroneseChartRingEquiv B q hf).toCommRingCatIso

def originalDegreeVeroneseBundledChartRes
    {e : ℕ} {f g x : V} (hg : g ∈ P e) (hx : x = f * g) :
    VC f ⟶ VC x :=
  CommRingCat.ofHom (awayMap P (f := f) hg hx)

def originalDegreeVeroneseBundledAmbientRes
    {e : ℕ} {f g x : V} (hg : g ∈ P e) (hxS : (x : S) = (f : S) * (g : S)) :
    SC f ⟶ SC x :=
  CommRingCat.ofHom (awayMap B (f := (f : S))
    (show (g : S) ∈ B (q * e) from hg) hxS)

/-- The product square as an equality in the category of commutative rings. -/
theorem originalDegreeVeroneseChartCommRingCatSquare
    {d e : ℕ} {f g x : V} (hf : f ∈ P d) (hg : g ∈ P e)
    (hx : x = f * g) (hxS : (x : S) = (f : S) * (g : S))
    (hxP : x ∈ P (d + e)) :
    originalDegreeVeroneseBundledChartRes B q hg hx ≫
      (originalDegreeVeroneseBundledChartIso B q hxP).hom =
    (originalDegreeVeroneseBundledChartIso B q hf).hom ≫
      originalDegreeVeroneseBundledAmbientRes B q hg hxS := by
  apply CommRingCat.hom_ext
  exact originalDegreeVeroneseChartRingHomSquare B q hf hg hx hxS hxP

end LinearStudy
#check LinearStudy.originalDegreeVeroneseChartCommRingCatSquare
#print axioms LinearStudy.originalDegreeVeroneseChartCommRingCatSquare

