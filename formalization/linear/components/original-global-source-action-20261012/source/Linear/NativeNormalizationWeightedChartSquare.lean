module
public import Linear.NativeNormalizationProjectiveMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
/-- The SAME actual normalization chart square holds in every positive degree, including degree-two overlaps. -/
theorem nativeNormalizationProjectiveMap_weighted_chart_square
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d) :
    Proj.awayι 𝓑 (algebraMap R S a)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) hd ≫
      nativeNormalizationProjectiveMap 𝒜 𝓑 =
    Spec.map (CommRingCat.ofHom
      (algebraMap (HomogeneousLocalization.Away 𝒜 a)
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))) ≫
      Proj.awayι 𝒜 a ha hd := by
  exact radicalProjMap_awayι_comp (normalizationBaseGradedRingHom 𝒜 𝓑)
    (finiteGradedNormalization_irrelevant_le_radical 𝒜 𝓑) hd a ha
/-- Actual restriction of the SAME global normalization, retaining positive-degree chart isomorphisms. -/
theorem nativeNormalizationProjectiveMap_weighted_chart_restriction
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d) :
    (nativeNormalizationProjectiveMap 𝒜 𝓑) ∣_ Proj.basicOpen 𝒜 a =
    (Proj.basicOpenIsoSpec 𝓑 (algebraMap R S a)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) hd).hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (HomogeneousLocalization.Away 𝒜 a)
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))) ≫
    (Proj.basicOpenIsoSpec 𝒜 a ha hd).inv := by
  apply (cancel_mono (Proj.basicOpen 𝒜 a).ι).mp
  have h := nativeNormalizationProjectiveMap_weighted_chart_square 𝒜 𝓑 d hd a ha
  have h' := congrArg (fun z =>
    (Proj.basicOpenIsoSpec 𝓑 (algebraMap R S a)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) hd).hom ≫ z) h
  with_unfolding_all simpa only [Proj.awayι,Category.assoc,Iso.hom_inv_id_assoc,
    morphismRestrict_ι,nativeNormalizationProjectiveMap_preimage_basicOpen] using h'
/-- The original intersection D_+(a)∩D_+(b) uses its actual degree-two Spec chart, not a degree-one replacement. -/
theorem nativeNormalizationProjectiveMap_overlap_chart_square
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) :
    Proj.awayι 𝓑 (algebraMap R S (a*b))
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (SetLike.mul_mem_graded ha hb)) (by decide) ≫
      nativeNormalizationProjectiveMap 𝒜 𝓑 =
    Spec.map (CommRingCat.ofHom
      (algebraMap (HomogeneousLocalization.Away 𝒜 (a*b))
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))))) ≫
      Proj.awayι 𝒜 (a*b) (SetLike.mul_mem_graded ha hb) (by decide) := by
  exact nativeNormalizationProjectiveMap_weighted_chart_square 𝒜 𝓑 2 (by decide) (a*b)
    (SetLike.mul_mem_graded ha hb)
end LinearStudy
