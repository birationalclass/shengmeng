module
public import Linear.NativeProjectiveGradedKernelCech
public import Linear.ModuleTopHomologyCokernelData
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

/-- Actual finite homogeneous surjections over a Noetherian graded ring
give cokernel data on top ordered Cech homology. The native kernel,
quasicoherence,affine exactness and next-degree vanishing are constructed
from the modules and their actual finite degree-one chart cover. -/
def nativeGradedKernelOrderedCech_topCokernelData [IsNoetherianRing S] [Module.Finite S E]
    (hb : Function.Surjective b) (k : ℤ) (q : ℕ) (hq : Fintype.card ι = q+1) :
    let T := ShortComplex.mk
      (nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k)
      (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh k)
      (nativeProjectiveKernelSheafInclusion_comp_zero 𝓑 ℰ ℱ hE hF b hh k)
    let G := Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))
    IsColimit (CokernelCofork.ofπ
      ((T.map G).map (HomologicalComplex.homologyFunctor
        (ModuleCat Γ(Y, (⊤ : Y.Opens))) (ComplexShape.up ℕ) q)).g
      ((T.map G).map (HomologicalComplex.homologyFunctor
        (ModuleCat Γ(Y, (⊤ : Y.Opens))) (ComplexShape.up ℕ) q)).zero) := by
  have hC := nativeProjectiveGradedKernelOrderedCech_shortExact 𝓑 ℰ ℱ hE hF b hh
    a ha hcover π hb k
  apply hC.homology_gIsCokernel_of_next_exact q (q+1) (by simp [ComplexShape.up_Rel])
  exact Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le π _ _ (q+1) (le_of_eq hq)

end LinearStudy
