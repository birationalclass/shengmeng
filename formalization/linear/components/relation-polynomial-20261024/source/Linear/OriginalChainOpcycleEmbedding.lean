module
public import Linear.ChainResolutionAsCochain
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
/-- Native opcycle comparison for SAME original n-to-minus-n embedding. -/
def originalChainAsCochainOpcyclesIso (C : ChainComplex A ℕ) (p : ℤ) (n : ℕ)
    (h : -(n : ℤ) = p) : (originalChainAsCochain C).opcycles p ≅ C.opcycles n :=
  C.extendOpcyclesIso ComplexShape.embeddingDownNat h
/-- SAME original quotient projection under native opcycle comparison. -/
theorem originalChainAsCochain_pOpcycles (C : ChainComplex A ℕ) (p : ℤ) (n : ℕ)
    (h : -(n : ℤ) = p) :
    (originalChainAsCochain C).pOpcycles p ≫ (originalChainAsCochainOpcyclesIso C p n h).hom =
      (originalChainAsCochainXIso C p n h).hom ≫ C.pOpcycles n :=
  C.pOpcycles_extendOpcyclesIso_hom ComplexShape.embeddingDownNat h
/-- SAME original induced differential on opcycles;retain both actual quotient maps. -/
theorem originalChainAsCochain_fromOpcycles (C : ChainComplex A ℕ) (p₁ p₂ : ℤ)
    (n₁ n₂ : ℕ) (h₁ : -(n₁ : ℤ) = p₁) (h₂ : -(n₂ : ℤ) = p₂) :
    (originalChainAsCochain C).fromOpcycles p₁ p₂ ≫ (originalChainAsCochainXIso C p₂ n₂ h₂).hom =
      (originalChainAsCochainOpcyclesIso C p₁ n₁ h₁).hom ≫ C.fromOpcycles n₁ n₂ := by
  apply (cancel_epi ((originalChainAsCochain C).pOpcycles p₁)).1
  calc
    _ = (originalChainAsCochain C).d p₁ p₂ ≫ (originalChainAsCochainXIso C p₂ n₂ h₂).hom := by
      rw [← Category.assoc,HomologicalComplex.p_fromOpcycles]
    _ = (originalChainAsCochainXIso C p₁ n₁ h₁).hom ≫ C.d n₁ n₂ := by
      rw [originalChainAsCochain_d C p₁ p₂ n₁ n₂ h₁ h₂]
      simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    _ = _ := by
      rw [← Category.assoc,originalChainAsCochain_pOpcycles,Category.assoc,
        HomologicalComplex.p_fromOpcycles]
end LinearStudy
