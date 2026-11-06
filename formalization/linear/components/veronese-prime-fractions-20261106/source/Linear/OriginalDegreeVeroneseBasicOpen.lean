module
public import Linear.OriginalDegreeVeroneseProjIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeroneseBasicOpenGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
local notation "I" => OriginalDegreeVeroneseChartIndex B q
local notation "C" => originalDegreeVeroneseAmbientAffineCover B q
local notation "D" => originalDegreeVeroneseRegradedAffineCover B q
local notation "E" => originalDegreeVeroneseIndexedAffineIso B q
local notation "F" => originalDegreeVeroneseProjHom B q

private theorem range_point_of_square
    {X Y U V : Type*} (fn : X → Y) (a : U → X) (b : V → Y) (i : U → V)
    (hinj : Function.Injective fn) (hsurj : Function.Surjective i)
    (hsquare : ∀ z, fn (a z) = b (i z))
    (s : Set X) (t : Set Y) (hs : Set.range a = s) (ht : Set.range b = t) (x : X) :
    fn x ∈ t ↔ x ∈ s := by
  rw [← hs, ← ht]
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨u,rfl⟩ := hsurj v
    exact ⟨u,hinj ((hsquare u).trans hv)⟩
  · rintro ⟨u,rfl⟩
    exact ⟨i u,(hsquare u).symm⟩

private theorem scheme_chart_point_of_square
    {X Y U W : Scheme.{v}} (e₀ : X ≅ Y) (e₁ : U ≅ W)
    (a : U ⟶ X) (b : W ⟶ Y) (h : a ≫ e₀.hom = e₁.hom ≫ b)
    (s : Set X) (t : Set Y)
    (hs : Set.range (fun z => a z) = s) (ht : Set.range (fun z => b z) = t) (x : X) :
    e₀.hom x ∈ t ↔ x ∈ s :=
  range_point_of_square e₀.hom a b e₁.hom
    (Scheme.homeoOfIso e₀).injective (Scheme.homeoOfIso e₁).surjective
    (fun z => by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : U ⟶ Y => m z) h)
    s t hs ht x

/-- The established scheme isomorphism identifies membership in
the common positive basic opens pointwise. -/
theorem originalDegreeVeroneseProjHom_mem_basicOpen_iff (i : I) (x : Proj B) :
    F x ∈ Proj.basicOpen P i.2.1 ↔ x ∈ Proj.basicOpen B (i.2.1 : S) := by
  have hC : Set.range (fun y => (C).f i y) = (Proj.basicOpen B (i.2.1 : S) : Set (Proj B)) :=
    congrArg (fun U : (Proj B).Opens => (U : Set (Proj B)))
      (originalDegreeVeroneseAmbientAwayImm_opensRange B q i)
  have hD : Set.range (fun y => (D).f i y) = (Proj.basicOpen P i.2.1 : Set (Proj P)) :=
    congrArg (fun U : (Proj P).Opens => (U : Set (Proj P)))
      (Proj.opensRange_awayι P i.2.1 i.2.2 i.1.2)
  exact scheme_chart_point_of_square (originalDegreeVeroneseProjIso B q) (E i)
    ((C).f i) ((D).f i) (originalDegreeVeroneseProjIso_hom_onChart B q i)
    _ _ hC hD x

end LinearStudy
#check LinearStudy.originalDegreeVeroneseProjHom_mem_basicOpen_iff
#print axioms LinearStudy.originalDegreeVeroneseProjHom_mem_basicOpen_iff

