module
public import Linear.OriginalDegreeVeroneseSpecChartRingSquare
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open HomogeneousLocalization AlgebraicGeometry CategoryTheory
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeroneseSpecChartGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

private theorem specBundledRingSquare
    {A₁ A₂ C₁ C₂ : CommRingCat.{v}}
    (a : A₁ ⟶ A₂) (c : C₁ ⟶ C₂)
    (e₁ : A₁ ≅ C₁) (e₂ : A₂ ≅ C₂)
    (h : a ≫ e₂.hom = e₁.hom ≫ c) :
    Spec.map c ≫ (Scheme.Spec.mapIso e₁.op).hom =
      (Scheme.Spec.mapIso e₂.op).hom ≫ Spec.map a := by
  change Spec.map c ≫ Spec.map e₁.hom = Spec.map e₂.hom ≫ Spec.map a
  rw [← Spec.map_comp, ← Spec.map_comp, h]

/-- The affine scheme comparison from the original chart to its regraded chart. -/
def originalDegreeVeroneseSpecChartIso
    {d : ℕ} {f : V} (hf : f ∈ P d) :
    Spec (originalDegreeVeroneseBundledAmbientChart B q f) ≅
      Spec (originalDegreeVeroneseBundledChart B q f) :=
  Scheme.Spec.mapIso (originalDegreeVeroneseBundledChartIso B q hf).op

/-- The affine scheme chart comparison commutes with each product inclusion. -/
theorem originalDegreeVeroneseSpecChartSquare
    {d e : ℕ} {f g x : V} (hf : f ∈ P d) (hg : g ∈ P e)
    (hx : x = f * g) (hxS : (x : S) = (f : S) * (g : S))
    (hxP : x ∈ P (d + e)) :
    Spec.map (originalDegreeVeroneseBundledAmbientRes B q hg hxS) ≫
      (originalDegreeVeroneseSpecChartIso B q hf).hom =
    (originalDegreeVeroneseSpecChartIso B q hxP).hom ≫
      Spec.map (originalDegreeVeroneseBundledChartRes B q hg hx) :=
  specBundledRingSquare
    (originalDegreeVeroneseBundledChartRes B q hg hx)
    (originalDegreeVeroneseBundledAmbientRes B q hg hxS)
    (originalDegreeVeroneseBundledChartIso B q hf)
    (originalDegreeVeroneseBundledChartIso B q hxP)
    (originalDegreeVeroneseChartCommRingCatSquare B q hf hg hx hxS hxP)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseSpecChartIso
#print axioms LinearStudy.originalDegreeVeroneseSpecChartIso
#check LinearStudy.originalDegreeVeroneseSpecChartSquare
#print axioms LinearStudy.originalDegreeVeroneseSpecChartSquare

