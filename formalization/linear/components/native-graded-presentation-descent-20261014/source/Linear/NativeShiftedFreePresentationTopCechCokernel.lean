module
public import Linear.NativeGradedPresentationTopCechQuotient
public import Linear.IntegerShiftedFreeDecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K S M I J ι : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (z : I → ℤ) (w : J → ℤ) (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ a : S, a ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → a • x ∈ 𝒟 ((n:ℤ)+d))
variable (c : (I → S) →ₗ[S] (J → S)) (b : (J → S) →ₗ[S] M)
variable (hrel : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z d →
  c x ∈ integerShiftedFreePiece 𝓑 w d)
variable (hquot : ∀ d : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece 𝓑 w d → b x ∈ 𝒟 d)
variable [Fintype ι] [LinearOrder ι]
variable (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
variable (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤)
variable {Y : Scheme.{u}} (π : Proj 𝓑 ⟶ Y)

/-- The ACTUAL shifted finite free presentation uses its constructed
integer gradings;its top native ordered-Cech homology is the cokernel
of its original relation-map homology. No cokernel is supplied as data. -/
def nativeShiftedFreePresentationOrderedCech_topCokernelIso [IsNoetherianRing S]
    (hb : Function.Surjective b) (hex : LinearMap.range c = b.ker)
    (k : ℤ) (q : ℕ) (hq : Fintype.card ι = q+1) :
    cokernel (HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))).map
        (nativeProjectiveDegreeZeroSheafMap 𝓑
          (integerShiftedFreePiece 𝓑 z) (integerShiftedFreePiece 𝓑 w)
          (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
          (integerShiftedFreePiece_smul_homogeneous 𝓑 w) c hrel k)) q) ≅
    (Scheme.Modules.orderedBaseCechComplex π (nativeProjectiveModuleSheaf 𝓑 𝒟 hD k)
      (fun i => Proj.basicOpen 𝓑 (a i))).homology q := by
  letI := integerShiftedFreeDecomposition 𝓑 z
  letI := integerShiftedFreeDecomposition 𝓑 w
  exact nativeGradedPresentationOrderedCech_topCokernelIso 𝓑
    (integerShiftedFreePiece 𝓑 z) (integerShiftedFreePiece 𝓑 w) 𝒟
    (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
    (integerShiftedFreePiece_smul_homogeneous 𝓑 w) hD
    c b hrel hquot a ha hcover π hb hex k q hq

/-- This comparison respects the ACTUAL original quotient map on
homology;no abstract vector-space isomorphism is chosen in its place. -/
theorem nativeShiftedFreePresentationOrderedCech_topCokernelIso_quotient [IsNoetherianRing S]
    (hb : Function.Surjective b) (hex : LinearMap.range c = b.ker)
    (k : ℤ) (q : ℕ) (hq : Fintype.card ι = q+1) :
    cokernel.π (HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))).map
        (nativeProjectiveDegreeZeroSheafMap 𝓑
          (integerShiftedFreePiece 𝓑 z) (integerShiftedFreePiece 𝓑 w)
          (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
          (integerShiftedFreePiece_smul_homogeneous 𝓑 w) c hrel k)) q) ≫
      (nativeShiftedFreePresentationOrderedCech_topCokernelIso 𝓑 z w 𝒟 hD
        c b hrel hquot a ha hcover π hb hex k q hq).hom =
    HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor π (fun i => Proj.basicOpen 𝓑 (a i))).map
        (nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 w) 𝒟
          (integerShiftedFreePiece_smul_homogeneous 𝓑 w) hD b hquot k)) q := by
  letI := integerShiftedFreeDecomposition 𝓑 z
  letI := integerShiftedFreeDecomposition 𝓑 w
  exact nativeGradedPresentationOrderedCech_topCokernelIso_quotient 𝓑
    (integerShiftedFreePiece 𝓑 z) (integerShiftedFreePiece 𝓑 w) 𝒟
    (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
    (integerShiftedFreePiece_smul_homogeneous 𝓑 w) hD
    c b hrel hquot a ha hcover π hb hex k q hq

end LinearStudy
