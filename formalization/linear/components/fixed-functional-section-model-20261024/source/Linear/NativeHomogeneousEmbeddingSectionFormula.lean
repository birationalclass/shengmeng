module
public import Linear.NativeHomogeneousShiftSectionMap
public import Linear.NativeDegreeZeroEmbeddingTarget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (DG : ℤ → Submodule K D) (EG : ℤ → Submodule K E)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ B n →
  ∀ ell : D, ell ∈ DG d → b • ell ∈ DG ((n : ℤ)+d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ B n →
  ∀ ell : E, ell ∈ EG d → b • ell ∈ EG ((n : ℤ)+d))

/-- Arithmetic twist transport retains the SAME element/1 section. -/
theorem nativeHomogeneousGlobalSection_indexTransport
    (k l : ℤ) (h : k=l) (ell : DG k) :
    ((eqToIso (congrArg (nativeProjectiveModuleSheaf B DG hD) h)).hom.app ⊤)
      (nativeProjectiveModuleHomogeneousGlobalSection B DG hD k ell) =
      nativeProjectiveModuleHomogeneousGlobalSection B DG hD l
        ⟨(ell:D),h ▸ ell.property⟩ := by
  subst l
  rfl
/-- Retain an ACTUAL zero-degree embedding and its EXACT action on every
homogeneous global section. The old existence theorem discarded this
section formula;here the SAME constructed map and original element are
retained for the subsequent ORIGINAL polynomial/support comparison. -/
theorem nativeProjectiveHomogeneousInjection_exists_zero_degree_mono_sectionFormula
    (delta : ℤ) (e : D →ₗ[S] E)
    (hh : ∀ d : ℤ,∀ ell : D,ell ∈ DG d → e ell ∈ EG (d+delta))
    (he : Function.Injective e) :
    ∃ j : nativeProjectiveModuleSheaf B DG hD 0 ⟶
        nativeProjectiveModuleSheaf B EG hE delta,
      Mono j ∧ ∀ ell : DG 0,
        (j.app ⊤) (nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 ell) =
          nativeProjectiveModuleHomogeneousGlobalSection B EG hE delta
            ⟨e (ell:D),by simpa only [zero_add] using hh 0 ell ell.property⟩ := by
  let f := nativeProjectiveModuleSheafMap B DG EG hD hE delta e hh 0
  letI : Mono f := nativeProjectiveModuleSheafMap_mono B DG EG hD hE delta e hh he 0
  let targetIso : nativeProjectiveModuleSheaf B EG hE (0+delta) ≅
      nativeProjectiveModuleSheaf B EG hE delta :=
    eqToIso (congrArg (nativeProjectiveModuleSheaf B EG hE) (zero_add delta))
  refine ⟨f ≫ targetIso.hom,inferInstance,?_⟩
  intro ell
  change (targetIso.hom.app ⊤) ((f.app ⊤)
    (nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 ell)) = _
  rw [nativeProjectiveModuleSheafMap_homogeneousGlobalSection]
  exact nativeHomogeneousGlobalSection_indexTransport B EG hE (0+delta) delta
    (zero_add delta) ⟨e (ell:D),hh 0 ell ell.property⟩
end LinearStudy
