module
public import Linear.NativeGradedKernelTopCechCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K S E F : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup E] [Module K E] [Module S E] [IsScalarTower K S E]
variable [AddCommGroup F] [Module K F] [Module S F] [IsScalarTower K S F]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (ℰ : ℤ → Submodule K E) (ℱ : ℤ → Submodule K F)
variable [DirectSum.Decomposition ℰ] [DirectSum.Decomposition ℱ]
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → c • x ∈ ℰ ((n:ℤ)+d))
variable (hF : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : F, x ∈ ℱ d → c • x ∈ ℱ ((n:ℤ)+d))
variable (b : E →ₗ[S] F) (hh : ∀ d : ℤ, ∀ x : E, x ∈ ℰ d → b x ∈ ℱ d)
variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
variable (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤)
variable {Y : Scheme.{u}} (π : Proj 𝓑 ⟶ Y)

/-- Actual homology of the native quotient sheaf is the cokernel of
its actual graded-kernel homology map,using the proved colimit data. -/
def nativeGradedKernelOrderedCech_topCokernelIso [IsNoetherianRing S] [Module.Finite S E]
    (hb : Function.Surjective b) (k : ℤ) (q : ℕ) (hq : Fintype.card ι = q+1) :
    cokernel (HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))).map
        (nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k)) q) ≅
    (Scheme.Modules.orderedBaseCechComplex π (nativeProjectiveModuleSheaf 𝓑 ℱ hF k)
      (fun i => Proj.basicOpen 𝓑 (a i))).homology q :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (nativeGradedKernelOrderedCech_topCokernelData 𝓑 ℰ ℱ hE hF b hh a ha hcover π hb k q hq)

theorem nativeGradedKernelOrderedCech_topCokernelIso_quotient [IsNoetherianRing S] [Module.Finite S E]
    (hb : Function.Surjective b) (k : ℤ) (q : ℕ) (hq : Fintype.card ι = q+1) :
    cokernel.π (HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))).map
        (nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k)) q) ≫
      (nativeGradedKernelOrderedCech_topCokernelIso 𝓑 ℰ ℱ hE hF b hh a ha hcover π hb k q hq).hom =
    HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))).map
        (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh k)) q := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (nativeGradedKernelOrderedCech_topCokernelData 𝓑 ℰ ℱ hE hF b hh a ha hcover π hb k q hq)
      WalkingParallelPair.one

end LinearStudy
