module
public import Linear.ActualAffineAlgebraDualSpecValue
public import Linear.NormalizationHomogeneousAffineDualOverlapLocalization
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
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
  LocalizedModule.moduleOfIsLocalization

theorem nativeActualAffineOverlapHom_original_elements_ext
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (h k : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
        (algebraMap (HomogeneousLocalization.Away 𝒜 (a*b))
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))))))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))))).ringCatSheaf))
      (SheafOfModules.unit (Spec (CommRingCat.of
        (HomogeneousLocalization.Away 𝒜 (a*b)))).ringCatSheaf),⊤))
    (H : ∀ x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a),
      let Aij := HomogeneousLocalization.Away 𝒜 (a*b)
      let Bij := HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))
      let γ := HomogeneousLocalization.awayMap 𝓑
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
        (map_mul (algebraMap R S) a b)
      schemeModuleHomSectionEvaluation _ _ ⊤ h
        ((actualAffineAlgebraStructurePushforwardIso (A := Aij) (B := Bij)).hom.app ⊤
          (tilde.toOpen (R := CommRingCat.of Aij) (ModuleCat.of Aij Bij) ⊤ (γ x))) =
      schemeModuleHomSectionEvaluation _ _ ⊤ k
        ((actualAffineAlgebraStructurePushforwardIso (A := Aij) (B := Bij)).hom.app ⊤
          (tilde.toOpen (R := CommRingCat.of Aij) (ModuleCat.of Aij Bij) ⊤ (γ x)))) :
    h = k := by
  let Ai := HomogeneousLocalization.Away 𝒜 a
  let Aij := HomogeneousLocalization.Away 𝒜 (a*b)
  let Bi := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let Bij := HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))
  letI := (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
  letI := normalizationHomogeneousOverlapSourceBaseAlgebra 𝒜 𝓑 1 1 a b ha hb
  letI := (HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
    (map_mul (algebraMap R S) a b)).toAlgebra
  letI := normalizationHomogeneousOverlapSource_scalarTower 𝒜 𝓑 1 1 a b ha hb
  letI : IsScalarTower Ai Aij Bij := IsScalarTower.of_algebraMap_eq' rfl
  letI := HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide : (1:ℕ)≠0)
  letI := normalizationHomogeneousOverlapSource_isLocalizedModule 𝒜 𝓑 1 1 a b ha hb (by decide)
  let ρ := (IsScalarTower.toAlgHom Ai Bi Bij).toLinearMap
  let E := actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := Aij) (B := Bij)
  obtain ⟨f,rfl⟩ := E.surjective h
  obtain ⟨g,rfl⟩ := E.surjective k
  have hv : ∀ x : Bi, f (ρ x) = g (ρ x) := by
    intro x
    have hx := H x
    dsimp only at hx
    rw [actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value,
      actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value] at hx
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
      (CommRingCat.of Aij)).inv).injective hx
  have he : f.restrictScalars Ai = g.restrictScalars Ai := by
    apply IsLocalizedModule.linearMap_ext
      (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb))
      ρ (Algebra.linearMap Ai Aij)
    exact LinearMap.ext hv
  apply congrArg E
  exact LinearMap.ext fun x => congr($(he) x)
end LinearStudy
