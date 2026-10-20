module
public import Linear.ProjectivePulledOriginalSetupSectionFamilyProof
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] projectivePulledOriginalCutActualSectionSequenceStatement
variable {n r : ℕ}
/-- ONE positive m above lower precedes ALL iterate maps,degrees and
normalizations. The SAME nonempty parameter open precedes ALL integer
k,with actual original quotient augmentations and the native cut-section
sequence at t=r*q-r-1. No Serre,augmentation or desired-exactness premise
is added. Inferred exact Prop proof type is audited explicitly;this is
not original4.1/4.2 or a final prescribed polynomial Q. -/
def projectivePulledOriginalSetup_uniformCutActualSectionSequenceProof
    (V : IntegralProjectiveEquations n) (lower : ℕ) (hr : 0 < r) (hrn : r < n) :=
  (projectivePulledOriginal_uniformCutActualSectionSequence_above V lower hr).imp
    (fun m hm => And.intro hm.1 (And.intro hm.2.1
      (fun (D : ℕ) (hD : 1 ≤ D) (f : HomogeneousEndomorphism n) (hd : m*D < f.degree)
        (hf : Function.Surjective f.onPoints) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
        (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
        (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
        (hfinite : (projectiveLinearNormalizationMap V L).Finite)
        (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) =>
          projectivePulledOriginalSetupCutActualSectionFamilyProof
            f V hrn (lt_of_le_of_lt (Nat.zero_le _) hd) hf hV L hL hinj hfinite x0 hx0
            (fun w e he => hm.2.2 D hD f hd L hL w e he))))
end LinearStudy
