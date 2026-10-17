module
public import Linear.SchemeModuleFiniteLocallyFreeInternalExt
public import Linear.NativeProjectiveIntegerTwistChartFree
public import Linear.NativeProjectiveDegreeOneCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- EVERY actual integer twist on native degree-one-generated Proj has
vanishing positive INTERNAL SHEAF Ext against ANY actual coefficient.
The cover and actual rank-one frames are PROVED from original grading. -/
theorem nativeIntegerTwistInternalExt_succ {ι : Type u} (a : ι → S)
    (ha : ∀ i, a i ∈ 𝓑 1) (hgen : Algebra.adjoin K (Set.range a) = ⊤)
    (k : ℤ) (N : (AlgebraicGeometry.Proj 𝓑).Modules) (q : ℕ) :
    IsZero (schemeModuleInternalExt
      (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k) N (q+1)) := by
  exact schemeModuleFiniteLocallyFreeInternalExt_succ_of_cover _ N
    (fun i => Proj.basicOpen 𝓑 (a i)) (degreeOneGenerated_nativeProj_cover 𝓑 a ha hgen)
    (fun _ => PUnit.{u+1}) (fun i =>
      (nativeIntegerTwistChartFreeIso 𝓑 (a i) (ha i) k
        (Proj.basicOpen 𝓑 (a i)) (fun p => p.2)).symm) q

end LinearStudy
