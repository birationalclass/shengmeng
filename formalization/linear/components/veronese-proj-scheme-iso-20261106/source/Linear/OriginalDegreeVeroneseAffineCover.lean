module
public import Linear.OriginalDegreeVeroneseSpecChart
public import Linear.OriginalDegreeVeroneseAmbientCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open HomogeneousLocalization AlgebraicGeometry CategoryTheory TopologicalSpace.Opens
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeroneseAffineCoverGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

local notation "I" => OriginalDegreeVeroneseChartIndex B q

/-- The original open immersion on a positive regraded denominator. -/
def originalDegreeVeroneseAmbientAwayImm (i : I) :
    Spec (originalDegreeVeroneseBundledAmbientChart B q i.2.1) ⟶ Proj B :=
  Proj.awayι B (i.2.1 : S) (m := q * (i.1 : ℕ)) i.2.2 (Nat.mul_pos hq.out i.1.2)

instance originalDegreeVeroneseAmbientAwayImmOpen (i : I) :
    IsOpenImmersion (originalDegreeVeroneseAmbientAwayImm B q i) := by
  let e := Proj.basicOpenIsoSpec B (i.2.1 : S) (m := q * (i.1 : ℕ)) i.2.2
    (Nat.mul_pos hq.out i.1.2)
  letI : IsIso e.inv := e.isIso_inv
  letI : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  change IsOpenImmersion (e.inv ≫ (Proj.basicOpen B (i.2.1 : S)).ι)
  exact IsOpenImmersion.comp _ _

theorem originalDegreeVeroneseAmbientAwayImm_opensRange (i : I) :
    (originalDegreeVeroneseAmbientAwayImm B q i).opensRange = Proj.basicOpen B (i.2.1 : S) :=
  Proj.opensRange_awayι B (i.2.1 : S) (m := q * (i.1 : ℕ)) i.2.2
    (Nat.mul_pos hq.out i.1.2)

theorem originalDegreeVeroneseAmbientIndex_exists (x : Proj B) :
    ∃ i : I, x ∈ Proj.basicOpen B (i.2.1 : S) := by
  have hx : x ∈ (⊤ : (Proj B).Opens) := trivial
  exact mem_iSup.mp ((originalDegreeVeroneseAmbientCover B q hq.out).symm ▸ hx)

/-- An affine cover of the original Proj by the common positive
Veronese chart indices. -/
def originalDegreeVeroneseAmbientAffineCover : (Proj B).AffineOpenCover where
  I₀ := I
  X i := originalDegreeVeroneseBundledAmbientChart B q i.2.1
  f i := originalDegreeVeroneseAmbientAwayImm B q i
  idx x := (originalDegreeVeroneseAmbientIndex_exists B q x).choose
  covers x := by
    let i := (originalDegreeVeroneseAmbientIndex_exists B q x).choose
    change x ∈ (originalDegreeVeroneseAmbientAwayImm B q i).opensRange
    rw [originalDegreeVeroneseAmbientAwayImm_opensRange]
    exact (originalDegreeVeroneseAmbientIndex_exists B q x).choose_spec

/-- The standard affine cover of regraded Proj, with the same indices. -/
def originalDegreeVeroneseRegradedAffineCover : (Proj P).AffineOpenCover :=
  Proj.affineOpenCover P

theorem originalDegreeVeroneseAffineCover_sameIndex :
    (originalDegreeVeroneseAmbientAffineCover B q).I₀ =
      (originalDegreeVeroneseRegradedAffineCover B q).I₀ := rfl

end LinearStudy
#check LinearStudy.originalDegreeVeroneseAmbientAffineCover
#print axioms LinearStudy.originalDegreeVeroneseAmbientAffineCover
#check LinearStudy.originalDegreeVeroneseRegradedAffineCover
#print axioms LinearStudy.originalDegreeVeroneseRegradedAffineCover
#check LinearStudy.originalDegreeVeroneseAffineCover_sameIndex
#print axioms LinearStudy.originalDegreeVeroneseAffineCover_sameIndex

