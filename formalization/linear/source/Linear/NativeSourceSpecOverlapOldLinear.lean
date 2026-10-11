module
public import Linear.NativeFiniteGradedChartOverlapLocalization
public import Linear.SchemeModuleSpecOpenNamedScalar
public import Linear.NativeProjectiveChartSectionsOverlap
public import Linear.NativeGradedDegreeOneOverlapLocalization
public import Linear.NativeSourceSpecChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable [IsNoetherianRing S] [Module.Finite S M] [IsDomain S] [Module.IsTorsionFree S M]
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeSourceSpecChartSectionsModule
/-- Bundle the OLD actual weighted Proj section map after actual source-Spec
transport as a linear map over the original one-chart ring. No compatibility
hypothesis is supplied: the genuine structure-ring scalar square proves it. -/
def nativeSourceSpecOverlapOldSectionLinearMap
    (a b : S) (ha : a ∈ 𝓑 1) (hb : b ∈ 𝓑 1) :
    let Q := (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).restrict (Proj.awayι 𝓑 a ha (by decide))
    let W : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).Opens :=
    PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem ha hb)
    letI := nativeGradedDegreeOneOverlapBaseModule 𝓑 𝒟 a b hb
    letI : Module (HomogeneousLocalization.Away 𝓑 a) Γ(Q,W) :=
      inferInstanceAs <| Module (HomogeneousLocalization.Away 𝓑 a)
        (((modulesSpecToSheaf (R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).obj Q).obj.obj (op W))
    nativeGradedModuleAwayDegreeZero 𝓑 𝒟 2 (a*b)
      →ₗ[HomogeneousLocalization.Away 𝓑 a] Γ(Q,W) := by
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  let j := Proj.awayι 𝓑 a ha (by decide)
  let Q := F.restrict j
  let W : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).Opens :=
    PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem ha hb)
  let U := Proj.basicOpen 𝓑 (a*b)
  let T := Proj.basicOpen 𝓑 a
  letI := nativeGradedDegreeOneOverlapBaseModule 𝓑 𝒟 a b hb
  letI : Module (HomogeneousLocalization.Away 𝓑 a) Γ(Q,W) :=
    inferInstanceAs <| Module (HomogeneousLocalization.Away 𝓑 a)
      (((modulesSpecToSheaf (R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).obj Q).obj.obj (op W))
  have hW : j ''ᵁ W = U := nativeProjectiveChartRatioOpen_image 𝓑 a b ha hb
  have hT : j ''ᵁ ⊤ = T := j.image_top_eq_opensRange.trans (Proj.opensRange_awayι 𝓑 a ha (by decide))
  let E := schemeModuleSpecOpenSectionsEquiv F j W U hW
  let q := nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 2 (a*b) (SetLike.mul_mem_graded ha hb)
  let ρ := HomogeneousLocalization.awayMap 𝓑 hb (rfl : a*b=a*b)
  have hφ : Proj.awayToSection 𝓑 a ≫ (Proj 𝓑).presheaf.map (eqToHom hT).op ≫
      (j.appIso ⊤).hom = (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).inv := by
    have hh : (Proj 𝓑).presheaf.map (eqToHom hT).op ≫ (j.appIso ⊤).hom =
        j.appLE T ⊤ (by rw [←hT]; exact (j.preimage_image_eq ⊤).ge) := by
      rw [Scheme.Hom.appIso_hom',Scheme.Hom.map_appLE']
    rw [hh]
    exact originalProjectiveChartScalar_appLE 𝓑 a ha
  exact {
    toFun := fun x => E (q x)
    map_add' := fun x y => by rw [q.map_add,E.map_add]
    map_smul' := fun r x => by
      change E (q (ρ r • x)) = r • E (q x)
      rw [q.map_smulₛₗ]
      have hr : (Proj.awayToSection 𝓑 (a*b)).hom (ρ r) =
          (Proj 𝓑).presheaf.map (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝓑 a b)).op
            (Proj.awayToSection 𝓑 a r) := by
        have H : CommRingCat.ofHom ρ ≫ Proj.awayToSection 𝓑 (a*b) =
            Proj.awayToSection 𝓑 a ≫ (Proj 𝓑).presheaf.map
              (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝓑 a b)).op :=
          Proj.awayMap_awayToSection 𝓑 hb (rfl : a*b=a*b)
        convert! congr($(H).hom r) using 1 <;> rfl
      exact (congrArg (fun c => E (c • q x)) hr).trans
        (schemeModuleSpecOpenSectionsEquiv_smul_namedImages F j W U T hW hT
          (Proj.awayToSection 𝓑 a) hφ r (q x)) }
end LinearStudy
