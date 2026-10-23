module
public import Linear.IntegerGradedFinitePresentation
public import Linear.NativeProjectiveSheafExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Classical
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n : ℤ) + d))
include hD

/-- A finite integer-graded module over the actual noetherian ring has
an ACTUAL homogeneous finite presentation whose original native Proj
associated sheaves form an exact complex and whose last map is epi.
Finite free MODULE sources are constructed; their free SHEAF chart
comparison is a separate obligation, not asserted here. -/
theorem nativeProjectiveFiniteGraded_exists_exact_native_presentation
    [IsNoetherianRing S] [Module.Finite S M] :
    ∃ s : Finset M,
      letI := Classical.decEq s
      ∃ w : s → ℤ,
        let ℰ := integerShiftedFreePiece 𝓑 w
        let hE := integerShiftedFreePiece_smul_homogeneous 𝓑 w
        letI := integerShiftedFreeDecomposition 𝓑 w
        let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
        ∃ hh : ∀ d : ℤ, ∀ f : s → S, f ∈ ℰ d → e f ∈ 𝒟 d,
          Function.Surjective e ∧
            Epi (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ 𝒟 hE hD e hh 0) ∧
            ∃ t : Finset e.ker,
              letI := Classical.decEq t
              ∃ z : t → ℤ,
                let ℛ := integerShiftedFreePiece 𝓑 z
                let hR := integerShiftedFreePiece_smul_homogeneous 𝓑 z
                letI := integerShiftedFreeDecomposition 𝓑 z
                let a := integerShiftedFreeGeneratorMap (S := S)
                  (fun i : t => ((i : e.ker) : s → S))
                ∃ ha : ∀ d : ℤ, ∀ f : t → S, f ∈ ℛ d → a f ∈ ℰ d,
                  ∃ hex : LinearMap.range a = e.ker,
                    (ShortComplex.mk
                      (nativeProjectiveDegreeZeroSheafMap 𝓑 ℛ ℰ hR hE a ha 0)
                      (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ 𝒟 hE hD e hh 0)
                      (nativeProjectiveDegreeZeroSheafMap_comp_zero 𝓑 ℛ ℰ 𝒟
                        hR hE hD a e ha hh hex 0)).Exact := by
  classical
  obtain ⟨s, w, he, hh, t, z, hex, ha⟩ :=
    integerGradedFinite_exists_shiftedFree_presentation 𝓑 𝒟 hD
  letI := integerShiftedFreeDecomposition 𝓑 w
  letI := integerShiftedFreeDecomposition 𝓑 z
  refine ⟨s, w, hh, he, ?_, t, z, ha, hex, ?_⟩
  · exact nativeProjectiveDegreeZeroSheafMap_epi 𝓑
      (integerShiftedFreePiece 𝓑 w) 𝒟
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) hD _ hh he 0
  · exact nativeProjectiveDegreeZeroSheafMap_exact 𝓑
      (integerShiftedFreePiece 𝓑 z) (integerShiftedFreePiece 𝓑 w) 𝒟
      (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) hD _ _ ha hh hex 0

end LinearStudy
