module
public import Linear.NativeProjectiveModuleTwistTensorSheafIso
public import Linear.ModuleOrderedBaseCechFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module S M] [Module K M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : M, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
variable {ι : Type u} [LinearOrder ι]
variable (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
variable (hgen : Algebra.adjoin K (Set.range a) = ⊤)
variable {Y : Scheme.{u}} (π : AlgebraicGeometry.Proj 𝓑 ⟶ Y)

/-- The checked actual native tensor-sheaf comparison induces the actual
isomorphism of ordered Cech complexes on the original degree-one opens.
Neither an external line-bundle-model comparison nor vanishing is assumed
or proved here. The actual Cech differential is the alternating restriction sum. -/
def nativeProjectiveTensorTwistOrderedCechIso (m : ℕ) (k : ℤ) :
    Scheme.Modules.orderedBaseCechComplex π
      (nativeProjectiveModuleTwistTensorSheaf 𝓑 𝒟 hD m k)
      (fun i => Proj.basicOpen 𝓑 (a i)) ≅
    Scheme.Modules.orderedBaseCechComplex π
      (nativeProjectiveModuleSheaf 𝓑 𝒟 hD (k+(m : ℤ)))
      (fun i => Proj.basicOpen 𝓑 (a i)) :=
  (Scheme.Modules.orderedBaseCechComplexFunctor π
    (fun i => Proj.basicOpen 𝓑 (a i))).mapIso
    (nativeProjectiveModuleTwistTensorSheafIso 𝓑 𝒟 hD a ha hgen m k)

include ha hgen in
/-- Exactness of the actual native tensor-twist Cech complex is equivalent
to exactness for the actual shifted local-fraction sheaf, in every degree. -/
theorem nativeProjectiveTensorTwistOrderedCech_exactAt_iff (m : ℕ) (k : ℤ) (q : ℕ) :
    (Scheme.Modules.orderedBaseCechComplex π
      (nativeProjectiveModuleTwistTensorSheaf 𝓑 𝒟 hD m k)
      (fun i => Proj.basicOpen 𝓑 (a i))).ExactAt q ↔
    (Scheme.Modules.orderedBaseCechComplex π
      (nativeProjectiveModuleSheaf 𝓑 𝒟 hD (k+(m : ℤ)))
      (fun i => Proj.basicOpen 𝓑 (a i))).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff_isZero_homology]
  exact (HomologicalComplex.homologyMapIso
    (nativeProjectiveTensorTwistOrderedCechIso 𝓑 𝒟 hD a ha hgen π m k) q).isZero_iff

/-- The actual native ordered Cech complex is exact above the cardinality
of its finite degree-one cover. This is only the induction base for Serre
vanishing; the positive-twist H1 bound remains a separate open obligation. -/
theorem nativeProjectiveIntegerTwistOrderedCech_exactAt_of_card_le
    [Fintype ι] (k : ℤ) (q : ℕ) (hq : Fintype.card ι ≤ q) :
    (Scheme.Modules.orderedBaseCechComplex π
      (nativeProjectiveModuleSheaf 𝓑 𝒟 hD k)
      (fun i => Proj.basicOpen 𝓑 (a i))).ExactAt q :=
  Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le π
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hD k)
    (fun i => Proj.basicOpen 𝓑 (a i)) q hq

end LinearStudy
