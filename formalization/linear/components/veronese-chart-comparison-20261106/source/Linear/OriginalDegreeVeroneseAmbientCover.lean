module
public import Linear.OriginalDegreeVeroneseAlgebra
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry TopologicalSpace.Opens
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]

/-- The indices of all positive regraded homogeneous charts. -/
def OriginalDegreeVeroneseChartIndex (q : ℕ) :=
  Σ i : PNat, originalDegreeVeronesePiece B q i

/-- The original Proj is covered by the very same homogeneous denominators
used for the Veronese Proj. The q-th power of an original denominator
lies in the regraded piece of its original degree. -/
theorem originalDegreeVeroneseAmbientCover (q : ℕ) (hq : 0 < q) :
    (⨆ i : OriginalDegreeVeroneseChartIndex B q,
      Proj.basicOpen B (i.2.1 : S)) = ⊤ := by
  classical
  apply top_le_iff.mp
  intro x hx
  have htop :
      (⨆ j : (Σ i : PNat, B i), Proj.basicOpen B (j.2 : S)) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    intro z hz
    rw [← DirectSum.sum_support_decompose B z]
    refine Ideal.sum_mem _ fun c hc ↦ if hc0 : c = 0 then ?_ else
      Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
    convert Ideal.zero_mem _
    subst hc0
    exact hz
  have hC : x ∈ (⨆ j : (Σ i : PNat, B i), Proj.basicOpen B (j.2 : S)) := htop.symm ▸ hx
  obtain ⟨j, hj⟩ := mem_iSup.mp hC
  have hpow : (j.2 : S) ^ q ∈ B (q * (j.1 : ℕ)) := by
    simpa only [nsmul_eq_mul, Nat.cast_id] using SetLike.pow_mem_graded q j.2.2
  let f : originalDegreeVeroneseAlgebra B q :=
    ⟨(j.2 : S) ^ q, originalDegreeVeroneseAlgebra_mem_of_mem B q j.1 hpow⟩
  have hf : f ∈ originalDegreeVeronesePiece B q j.1 := hpow
  refine mem_iSup.mpr ⟨⟨j.1, f, hf⟩, ?_⟩
  change x ∈ Proj.basicOpen B ((j.2 : S) ^ q)
  rwa [Proj.basicOpen_pow _ _ q hq]

end LinearStudy
#check LinearStudy.OriginalDegreeVeroneseChartIndex
#print axioms LinearStudy.OriginalDegreeVeroneseChartIndex
#check LinearStudy.originalDegreeVeroneseAmbientCover
#print axioms LinearStudy.originalDegreeVeroneseAmbientCover

