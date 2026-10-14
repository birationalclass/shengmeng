module
public import Linear.NativeGradedKernelTopCechCokernelIso
public import Linear.NativeProjectiveDegreeZeroComposition
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

/-- For an ACTUAL homogeneous presentation R->E->M over a Noetherian
graded ring,with finite R,E,surjective b and range(c)=ker(b),top native
Cech homology of M is the cokernel of the ACTUAL relation homology map.
The relation need not be injective. Its surjection onto the actual kernel
and the required top homology epimorphism are proved,not assumed. -/
def nativeGradedPresentationOrderedCech_topCokernelIso
    [IsNoetherianRing S] [Module.Finite S R] [Module.Finite S E]
    (hb : Function.Surjective b) (hex : LinearMap.range c = b.ker)
    (k : ℤ) (q : ℕ) (hq : Fintype.card ι = q+1) :
    cokernel (HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))).map
        (nativeProjectiveDegreeZeroSheafMap 𝓑 ℛ ℰ hR hE c hrel k)) q) ≅
    (Scheme.Modules.orderedBaseCechComplex π (nativeProjectiveModuleSheaf 𝓑 𝒟 hD k)
      (fun i => Proj.basicOpen 𝓑 (a i))).homology q := by
  let 𝒦 := nativeProjectiveKernelPiece ℰ b
  let hK := nativeProjectiveKernelPiece_graded 𝓑 ℰ b hE
  letI := nativeProjectiveKernelDecomposition ℰ 𝒟 b hquot
  have hm : ∀ x : R, c x ∈ b.ker := fun x => hex ▸ ⟨x, rfl⟩
  let c0 : R →ₗ[S] b.ker := c.codRestrict b.ker hm
  have hc0 : ∀ d : ℤ, ∀ x : R, x ∈ ℛ d → c0 x ∈ 𝒦 d := fun d x hx => hrel d x hx
  have hs : Function.Surjective c0 := by
    intro x
    have hx : (x : E) ∈ LinearMap.range c := hex.symm ▸ x.property
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  let α := nativeProjectiveDegreeZeroSheafMap 𝓑 ℛ ℰ hR hE c hrel k
  let γ := nativeProjectiveDegreeZeroSheafMap 𝓑 ℛ 𝒦 hR hK c0 hc0 k
  let δ := nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k
  have hfac : γ ≫ δ = α := by
    change nativeProjectiveDegreeZeroSheafMap 𝓑 ℛ 𝒦 hR hK c0 hc0 k ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 𝒦 ℰ hK hE b.ker.subtype (fun _ _ hx => hx) k = _
    erw [nativeProjectiveDegreeZeroSheafMap_comp]
    rfl
  let G := Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))
  let H := HomologicalComplex.homologyFunctor (ModuleCat Γ(Y, (⊤ : Y.Opens))) (ComplexShape.up ℕ) q
  let L := G ⋙ H
  have hγ := nativeGradedKernelOrderedCech_topCokernelData 𝓑 ℛ 𝒦 hR hK c0 hc0
    a ha hcover π hs k q hq
  letI : Epi (L.map γ) := epi_of_isColimit_cofork hγ
  have hα : L.map α = L.map γ ≫ L.map δ := by
    rw [← Functor.map_comp, hfac]
  exact cokernelIsoOfEq hα ≪≫ cokernelEpiComp (L.map γ) (L.map δ) ≪≫
    nativeGradedKernelOrderedCech_topCokernelIso 𝓑 ℰ 𝒟 hE hD b hquot a ha hcover π hb k q hq

end LinearStudy
