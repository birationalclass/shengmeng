module
public import Linear.NativeBaseSourceChartSections
public import Linear.SchemeModuleSpecChartSections
public import Linear.OriginalProjectiveChartSectionRing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ)+d))
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

@[instance_reducible] def nativeSourceSpecChartSectionsModule (a : S) (ha : a ∈ 𝓑 1) :
    Module (HomogeneousLocalization.Away 𝓑 a)
      Γ((nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).restrict
        (Proj.awayι 𝓑 a ha (by decide)),⊤) :=
  inferInstanceAs <| Module (HomogeneousLocalization.Away 𝓑 a)
    ((moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).obj
      ((nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).restrict (Proj.awayι 𝓑 a ha (by decide))))
attribute [local instance] nativeSourceSpecChartSectionsModule

/-- Original local fractions into sections of the SAME actual source sheaf restricted to Spec. -/
def nativeSourceSpecChartSectionLinearMap (a : S) (ha : a ∈ 𝓑 1) :
    nativeGradedModuleAwayZero 𝓑 𝒟 a →ₗ[HomogeneousLocalization.Away 𝓑 a]
      Γ((nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).restrict
        (Proj.awayι 𝓑 a ha (by decide)),⊤) := by
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  let j := Proj.awayι 𝓑 a ha (by decide)
  let U := Proj.basicOpen 𝓑 a
  have hi : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans (Proj.opensRange_awayι 𝓑 a ha (by decide))
  let E := schemeModuleSpecChartSectionsEquiv F j U hi
  let q := nativeProjectiveZeroChartSectionMap 𝓑 𝒟 hD a ha
  exact {
    toFun := fun x => E (q x)
    map_add' := fun x y => by rw [q.map_add,E.map_add]
    map_smul' := fun c x => by
      rw [q.map_smulₛₗ]
      have ht := schemeModuleSpecChartSectionsEquiv_smul F j U hi
        (Proj.awayToSection 𝓑 a) (originalProjectiveChartScalar_appLE 𝓑 a ha) c (q x)
      change E (Proj.awayToSection 𝓑 a c • q x) =
        (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).inv c • E (q x)
      exact ht }

theorem nativeSourceSpecChartSectionLinearMap_bijective (a : S) (ha : a ∈ 𝓑 1)
    (h : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1 a ha)) :
    Function.Bijective (nativeSourceSpecChartSectionLinearMap 𝓑 𝒟 hD a ha) := by
  exact (schemeModuleSpecChartSectionsEquiv
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0) (Proj.awayι 𝓑 a ha (by decide))
    (Proj.basicOpen 𝓑 a) ((Proj.awayι 𝓑 a ha (by decide)).image_top_eq_opensRange.trans
      (Proj.opensRange_awayι 𝓑 a ha (by decide)))).bijective.comp
        (nativeProjectiveZeroChartSectionMap_bijective 𝓑 𝒟 hD a ha h)

end LinearStudy
