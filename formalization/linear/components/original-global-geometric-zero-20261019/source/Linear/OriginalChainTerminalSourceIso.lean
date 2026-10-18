module
public import Linear.OriginalChainIteratedSourceBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
attribute [local instance] originalChainAugmentationAsCochain_quasiIso
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
/-- CONSTRUCT the SAME original canonical terminal quotient isomorphism from actual alpha alone. -/
def originalChainTerminalSourceIso (C : ChainComplex A ℕ) {E : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha) :
    (originalChainAsCochain C).opcycles (cochainSourceDegree r r) ≅ E := by
  letI := hAlpha
  haveI : (originalChainAsCochain C).IsStrictlyLE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyLE (C.extend ComplexShape.embeddingDownNat) 0)
  haveI := cochainAugmentationOpcycle_isIso (originalChainAugmentationAsCochain C alpha)
  haveI : IsIso (cochainSourceTerminalMap r
      (cochainAugmentationOpcycle (originalChainAugmentationAsCochain C alpha))) := by
    unfold cochainSourceTerminalMap
    infer_instance
  exact asIso (cochainSourceTerminalMap r
    (cochainAugmentationOpcycle (originalChainAugmentationAsCochain C alpha)))
/-- The actual isomorphism retains EXACT original terminal augmentation map and endpoint transport. -/
theorem originalChainTerminalSourceIso_hom (C : ChainComplex A ℕ) {E : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha) :
    (originalChainTerminalSourceIso C r alpha hAlpha).hom =
      cochainSourceTerminalMap r (cochainAugmentationOpcycle (originalChainAugmentationAsCochain C alpha)) := rfl
end LinearStudy
