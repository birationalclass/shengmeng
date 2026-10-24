module
public import Linear.SchemeModuleOriginalBoundarySequenceComparison
public import Linear.SchemeModuleChainOpcycleExtShift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- Every USED positive-degree boundary is an isomorphism,derived from ACTUAL source-term internal Ext vanishing. -/
theorem schemeModuleOriginalNatBoundaryStep_isIso
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (I : InjectiveResolution N)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (C.X p) N (j+1)))
    (n : ℕ) (hn : 0 < n) (hnr : n < r) :
    IsIso (schemeModuleOriginalNatBoundaryStep C N r alpha hAlpha n) := by
  letI := hAlpha
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [schemeModuleOriginalNatBoundaryStep_eq C N r alpha hAlpha (q+1) hnr,
    schemeModuleInternalExtSourceBoundary_eq_viaResolution _ _ N I (q+1)]
  change IsIso (eqToHom _ ≫
    (schemeModuleChainOpcycleExtShiftIso C (r-((q+1)+1))
      (originalChainAugmentation_exactAt_succ C alpha _) N I q (hA _)).hom)
  infer_instance
/-- The finite POSITIVE boundary tail is invertible;no isomorphism of the first degree-zero boundary is asserted. -/
theorem schemeModuleOriginalNatPositiveTail_isIso
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (I : InjectiveResolution N)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (C.X p) N (j+1)))
    (n : ℕ) (hn : 1 ≤ n) (hnr : n ≤ r) :
    IsIso (Functor.OfSequence.map (schemeModuleOriginalNatBoundaryStep C N r alpha hAlpha) 1 n hn) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      rw [Functor.OfSequence.map_id]
      infer_instance
    · rw [Functor.OfSequence.map_comp _ 1 n (n+1) (by omega) (by omega),
        Functor.OfSequence.map_le_succ]
      haveI := ih (by omega) (by omega)
      haveI := schemeModuleOriginalNatBoundaryStep_isIso C N r alpha hAlpha I hA n (by omega) (by omega)
      infer_instance
/-- SAME original positive boundary tail as an actual constructed isomorphism. -/
def schemeModuleOriginalNatPositiveTailIso
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (I : InjectiveResolution N)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (C.X p) N (j+1)))
    (n : ℕ) (hn : 1 ≤ n) (hnr : n ≤ r) :
    schemeModuleInternalExt (C.opcycles (r-1)) N 1 ≅
      schemeModuleInternalExt (C.opcycles (r-n)) N n := by
  letI := schemeModuleOriginalNatPositiveTail_isIso C N r alpha hAlpha I hA n hn hnr
  exact asIso (Functor.OfSequence.map (schemeModuleOriginalNatBoundaryStep C N r alpha hAlpha) 1 n hn)
/-- Retain the exact actual native sequence map,including its original index transports. -/
theorem schemeModuleOriginalNatPositiveTailIso_hom
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (I : InjectiveResolution N)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (C.X p) N (j+1)))
    (n : ℕ) (hn : 1 ≤ n) (hnr : n ≤ r) :
    (schemeModuleOriginalNatPositiveTailIso C N r alpha hAlpha I hA n hn hnr).hom =
      Functor.OfSequence.map (schemeModuleOriginalNatBoundaryStep C N r alpha hAlpha) 1 n hn := rfl
end LinearStudy
