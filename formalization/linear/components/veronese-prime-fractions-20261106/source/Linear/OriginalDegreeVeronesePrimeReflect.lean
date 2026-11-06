module
public import Linear.OriginalDegreeVeronesePrimeLocalization
public import Linear.OriginalDegreeVeronesePrimeAnnihilator
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u v w
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeronesePrimeReflectGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "F" => originalDegreeVeroneseProjHom B q

local notation "Q" => originalDegreeVeroneseRegradedPrimeCompl B q
local notation "T" => originalDegreeVeroneseAmbientPrimeCompl B

variable {M : Type w} [AddCommGroup M] [Module K M] [Module S M]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ a : M, a ∈ D d → c • a ∈ D ((n : ℤ) + d))
local notation "W" => originalDegreeVeroneseCoefficient B D hD q

private theorem smul_cross_eq_of_smul_sub_eq_zero (c : S) (a b : M)
    (h : c • (a - b) = 0) : c • a = c • b :=
  sub_eq_zero.mp ((smul_sub c a b).symm.trans h)

private theorem veronese_mk_eq_of_cross (x : Proj B)
    (a b : W) (s t u : Q x)
    (hu : ((u : V) : S) •
      (((t : V) : S) • (a : M) - ((s : V) : S) • (b : M)) = 0) :
    LocalizedModule.mk a s = LocalizedModule.mk b t := by
  apply LocalizedModule.mk_eq.mpr
  refine ⟨u, Subtype.ext ?_⟩
  change ((u : V) : S) • (((t : V) : S) • (a : M)) =
    ((u : V) : S) • (((s : V) : S) • (b : M))
  exact smul_cross_eq_of_smul_sub_eq_zero _ _ _ hu

variable [DirectSum.Decomposition D]

/-- Equality of fractions in the original localization reflects to the
contracted prime when the cross difference is homogeneous. -/
theorem originalDegreeVeronesePrimeLocalization_reflect
    (x : Proj B) (a b : W) (s t : Q x) (d : ℤ)
    (hd : ((t : V) : S) • (a : M) - ((s : V) : S) • (b : M) ∈ D d)
    (h : LocalizedModule.mk (a : M) (originalDegreeVeronesePrimeDenominator B q x s) =
      LocalizedModule.mk (b : M) (originalDegreeVeronesePrimeDenominator B q x t)) :
    LocalizedModule.mk a s = LocalizedModule.mk b t := by
  obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp h
  have hc' : (c : S) • (((t : V) : S) • (a : M) - ((s : V) : S) • (b : M)) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.mpr hc
  obtain ⟨u, hu⟩ := originalDegreeVeronesePrimeAnnihilator B q D hD x d _ hd c c.property hc'
  exact veronese_mk_eq_of_cross B q D hD x a b s t u hu

end LinearStudy
#check LinearStudy.originalDegreeVeronesePrimeLocalization_reflect
#print axioms LinearStudy.originalDegreeVeronesePrimeLocalization_reflect

