module
public import Linear.RadicalProjMap
public import Linear.FiniteGradedNormalizationIrrelevantRadical
public import Linear.NativeNormalizationAffineFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- The actual original graded finite normalization constructs a global
scheme morphism on the native Proj objects. Its no-base-locus condition
is proved by finite generation, not supplied as a separate input. -/
def nativeNormalizationProjectiveMap : Proj 𝓑 ⟶ Proj 𝒜 :=
  radicalProjMap (normalizationBaseGradedRingHom 𝒜 𝓑)
    (finiteGradedNormalization_irrelevant_le_radical 𝒜 𝓑)

theorem nativeNormalizationProjectiveMap_preimage_basicOpen (a : R) :
    nativeNormalizationProjectiveMap 𝒜 𝓑 ⁻¹ᵁ Proj.basicOpen 𝒜 a =
      Proj.basicOpen 𝓑 (algebraMap R S a) := rfl

/-- The global original projection agrees with the same original
complete affine-chart algebra map used in the proved sheaf duality. -/
theorem nativeNormalizationProjectiveMap_chart_square (a : R) (ha : a ∈ 𝒜 1) :
    Proj.awayι 𝓑 (algebraMap R S a)
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) (by decide) ≫
      nativeNormalizationProjectiveMap 𝒜 𝓑 =
    Spec.map (CommRingCat.ofHom
        (algebraMap (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))) ≫
      Proj.awayι 𝒜 a ha (by decide) := by
  exact radicalProjMap_awayι_comp (normalizationBaseGradedRingHom 𝒜 𝓑)
    (finiteGradedNormalization_irrelevant_le_radical 𝒜 𝓑) (by decide) a ha

/-- Identify the actual restriction of the global projection with the
proved finite affine-chart morphism through native chart isomorphisms. -/
theorem nativeNormalizationProjectiveMap_chart_restriction (a : R) (ha : a ∈ 𝒜 1) :
    (nativeNormalizationProjectiveMap 𝒜 𝓑) ∣_ Proj.basicOpen 𝒜 a =
      (Proj.basicOpenIsoSpec 𝓑 (algebraMap R S a)
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) (by decide)).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))) ≫
      (Proj.basicOpenIsoSpec 𝒜 a ha (by decide)).inv := by
  apply (cancel_mono (Proj.basicOpen 𝒜 a).ι).mp
  have h := nativeNormalizationProjectiveMap_chart_square 𝒜 𝓑 a ha
  have h' := congrArg (fun z =>
    (Proj.basicOpenIsoSpec 𝓑 (algebraMap R S a)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) (by decide)).hom ≫ z) h
  with_unfolding_all simpa only [Proj.awayι,Category.assoc,Iso.hom_inv_id_assoc,
    morphismRestrict_ι,nativeNormalizationProjectiveMap_preimage_basicOpen] using h'

theorem nativeNormalizationProjectiveMap_chart_isFinite (a : R) (ha : a ∈ 𝒜 1) :
    IsFinite ((nativeNormalizationProjectiveMap 𝒜 𝓑) ∣_ Proj.basicOpen 𝒜 a) := by
  rw [nativeNormalizationProjectiveMap_chart_restriction 𝒜 𝓑 a ha]
  letI := nativeNormalizationAffineChart_isFinite 𝒜 𝓑 a ha
  infer_instance

/-- If original degree-one charts cover the target, the same global
normalization morphism is finite; no global finite-map certificate is given. -/
theorem nativeNormalizationProjectiveMap_isFinite_of_cover {ι : Type u}
    (a : ι → R) (ha : ∀ i, a i ∈ 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i)) = ⊤) :
    IsFinite (nativeNormalizationProjectiveMap 𝒜 𝓑) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun i => Proj.basicOpen 𝒜 (a i)) hcover
  exact fun i => nativeNormalizationProjectiveMap_chart_isFinite 𝒜 𝓑 (a i) (ha i)

end LinearStudy
