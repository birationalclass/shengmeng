module
public import Linear.NativeSourceSpecOpenSectionsModule
public import Linear.NativeSourceSpecChartLinear
public import Linear.NativeProjectiveChartSectionsOverlap
public import Linear.SchemeModuleSpecOpenNamedScalar
public import Linear.LocalizedSectionFunctionSurjective
public import Linear.NativeWeightedSpecSectionFunctionScalar
public import Mathlib.Algebra.Group.Action.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ,∀ d : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D d → c • x ∈ D ((n : ℤ)+d))
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeSourceSpecChartSectionsModule
attribute [local irreducible] nativeProjectiveChartDegreeZeroSectionMap
/-- Actual weighted chart surjectivity from the SAME one-chart comparison and
actual quasicoherence. The proof uses only denominator-compatible FUNCTIONS,
not a separately packaged overlap linear map or a source-localization premise.
The second factor has any positive degree;no domain or torsion-free assumption.
Native mathlib isLocalization_mul and actual Spec-open restriction are reused. -/
theorem nativeWeightedChartSectionMap_surjective_of_actualChart_function
    [(nativeProjectiveModuleSheaf B D hD 0).IsQuasicoherent]
    (e : ℕ) (he : 0 < e) (a b : S) (ha : a ∈ B 1) (hb : b ∈ B e)
    (hs : Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hD 1 a ha)) :
    Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hD (1+e) (a*b)
      (SetLike.mul_mem_graded ha hb)) := by
  let F := nativeProjectiveModuleSheaf B D hD 0
  let j := Proj.awayι B a ha (by decide)
  let Q := F.restrict j
  let Ai := HomogeneousLocalization.Away B a
  let Aij := HomogeneousLocalization.Away B (a*b)
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  let W : (Spec (CommRingCat.of Ai)).Opens := PrimeSpectrum.basicOpen t
  let U := Proj.basicOpen B (a*b)
  let N := nativeGradedModuleAwayDegreeZero B D (1+e) (a*b)
  let rho := HomogeneousLocalization.awayMap B hb (rfl : a*b=a*b)
  letI : Module Ai N := Module.compHom N rho
  letI := nativeSourceSpecOpenSectionsModule B D hD a ha W
  have hW : j ''ᵁ W = U := nativeWeightedProjRatioOpen_image B e he a b ha hb
  have hT : j ''ᵁ ⊤ = Proj.basicOpen B a :=
    j.image_top_eq_opensRange.trans (Proj.opensRange_awayι B a ha (by decide))
  let E := schemeModuleSpecOpenSectionsEquiv F j W U hW
  let E0 := LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one B D a)
  let f := nativeGradedModuleWeightedOverlapMap B D hD 1 e a b ha hb
  let theta0 : nativeGradedModuleAwayDegreeZero B D 1 a →
      ((modulesSpecToSheaf (R := CommRingCat.of Ai)).obj Q).obj.obj (op ⊤) :=
    fun x => nativeSourceSpecChartSectionLinearMap B D hD a ha (E0 x)
  let psi := (((modulesSpecToSheaf (R := CommRingCat.of Ai)).obj Q).obj.map W.leTop.op).hom
  let w := nativeProjectiveChartDegreeZeroSectionMap B D hD (1+e) (a*b)
    (SetLike.mul_mem_graded ha hb)
  let theta1 : N → ((modulesSpecToSheaf (R := CommRingCat.of Ai)).obj Q).obj.obj (op W) :=
    fun y => E (w y)
  letI : Q.IsQuasicoherent := inferInstance
  letI : IsLocalizedModule (Submonoid.powers t) psi :=
    (isIso_fromTildeΓ_iff_isLocalizing Q).mp inferInstance t
  have h0 : Function.Surjective theta0 := by
    intro s
    let Et := schemeModuleSpecChartSectionsEquiv F j (Proj.basicOpen B a) hT
    obtain ⟨v,hv⟩ := Et.surjective s
    obtain ⟨x,hx⟩ := hs v
    refine ⟨x,?_⟩
    change Et (nativeProjectiveChartDegreeZeroSectionMap B D hD 1 a ha x) = s
    rw [hx,hv]
  have hscalar : ∀ (s : Submonoid.powers t) (y : N),
      theta1 ((s : Ai) • y) = (s : Ai) • theta1 y := by
    intro s y
    change E (w (rho (s : Ai) • y)) = (s : Ai) • E (w y)
    exact nativeWeightedSpecSectionFunction_smul B D hD e he a b ha hb (s : Ai) y
  have hcomm : ∀ x,theta1 (f x) = psi (theta0 x) := by
    intro x
    have H := schemeModuleSpecOpenSectionsEquiv_restrict F j W ⊤ U (Proj.basicOpen B a)
      hW hT le_top (nativeProjectiveChartDegreeZeroSectionMap B D hD 1 a ha x)
    have ho : F.presheaf.map
        (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left B a b)).op
        (nativeProjectiveChartDegreeZeroSectionMap B D hD 1 a ha x) =
        nativeProjectiveChartDegreeZeroSectionMap B D hD (1+e) (a*b)
          (SetLike.mul_mem_graded ha hb) (f x) :=
      nativeProjectiveChartDegreeZeroSectionMap_overlap B D hD 1 e a b ha hb x
    exact (congrArg E ho).symm.trans H
  letI : Algebra Ai Aij := rho.toAlgebra
  letI : IsLocalization.Away t Aij :=
    HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide)
  have hdivide : ∀ s : Submonoid.powers t,Function.Surjective (fun y : N => (s : Ai) • y) := by
    intro s
    change Function.Surjective (fun y : N => rho (s : Ai) • y)
    have hu : IsUnit (rho (s : Ai)) := IsLocalization.map_units Aij s
    exact hu.smul_bijective.surjective
  have h1 : Function.Surjective theta1 :=
    localizedSectionFunction_surjective (Submonoid.powers t) psi (fun x => f x)
      theta0 theta1 hdivide hscalar h0 hcomm
  intro s
  obtain ⟨x,hx⟩ := h1 (E s)
  exact ⟨x,E.injective hx⟩
end LinearStudy
