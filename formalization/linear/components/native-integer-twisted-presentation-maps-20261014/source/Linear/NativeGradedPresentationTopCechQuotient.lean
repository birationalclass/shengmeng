module
public import Linear.NativeGradedPresentationTopCechCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K S R E M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup R] [Module K R] [Module S R] [IsScalarTower K S R]
variable [AddCommGroup E] [Module K E] [Module S E] [IsScalarTower K S E]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (ℛ : ℤ → Submodule K R) (ℰ : ℤ → Submodule K E) (𝒟 : ℤ → Submodule K M)
variable [DirectSum.Decomposition ℛ] [DirectSum.Decomposition ℰ] [DirectSum.Decomposition 𝒟]
variable (hR : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : R, x ∈ ℛ d → c • x ∈ ℛ ((n:ℤ)+d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → c • x ∈ ℰ ((n:ℤ)+d))
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n:ℤ)+d))
variable (c : R →ₗ[S] E) (b : E →ₗ[S] M)
variable (hrel : ∀ d : ℤ, ∀ x : R, x ∈ ℛ d → c x ∈ ℰ d)
variable (hquot : ∀ d : ℤ, ∀ x : E, x ∈ ℰ d → b x ∈ 𝒟 d)
variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
variable (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤)
variable {Y : Scheme.{u}} (π : Proj 𝓑 ⟶ Y)

/-- The actual graded-presentation comparison takes its cokernel quotient
map to the actual original quotient-map homology. This compatibility is
required before composing with polynomial duality or restriction. -/
theorem nativeGradedPresentationOrderedCech_topCokernelIso_quotient
    [IsNoetherianRing S] [Module.Finite S R] [Module.Finite S E]
    (hb : Function.Surjective b) (hex : LinearMap.range c = b.ker)
    (k : ℤ) (q : ℕ) (hq : Fintype.card ι = q+1) :
    cokernel.π (HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))).map
        (nativeProjectiveDegreeZeroSheafMap 𝓑 ℛ ℰ hR hE c hrel k)) q) ≫
      (nativeGradedPresentationOrderedCech_topCokernelIso 𝓑 ℛ ℰ 𝒟 hR hE hD
        c b hrel hquot a ha hcover π hb hex k q hq).hom =
    HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))).map
        (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ 𝒟 hE hD b hquot k)) q := by
  unfold nativeGradedPresentationOrderedCech_topCokernelIso
  simp only [Iso.trans_hom]
  erw [π_comp_cokernelIsoOfEq_hom_assoc]
  erw [Iso.trans_hom, cokernelEpiComp_hom, cokernel.π_desc_assoc]
  exact nativeGradedKernelOrderedCech_topCokernelIso_quotient 𝓑 ℰ 𝒟 hE hD b hquot
    a ha hcover π hb k q hq

end LinearStudy
