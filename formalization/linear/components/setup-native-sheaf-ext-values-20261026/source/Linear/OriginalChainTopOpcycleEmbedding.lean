module
public import Linear.OriginalChainOpcycleEmbedding
public import Linear.OriginalChainIteratedSourceBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [HasDerivedCategory.{d} A]
/-- SAME original top functional descends compatibly through the native cochain/chain quotient isomorphism. -/
theorem originalChainTopOpcycleFunctional_embedding (C : ChainComplex A ℕ) {N : A}
    (r : ℕ) (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    originalChainTopOpcycleFunctional C r a ha =
      (originalChainAsCochainOpcyclesIso C (-(r : ℤ)) r rfl).hom ≫
        C.descOpcycles a (r+1) (by simp) ha := by
  apply (cancel_epi ((originalChainAsCochain C).pOpcycles (-(r : ℤ)))).1
  calc
    _ = (originalChainAsCochainXIso C (-(r : ℤ)) r rfl).hom ≫ a := by
      dsimp only [originalChainTopOpcycleFunctional,cochainTopOpcycleFunctional]
      rw [HomologicalComplex.p_descOpcycles]
    _ = _ := by
      rw [← Category.assoc,originalChainAsCochain_pOpcycles,Category.assoc,
        HomologicalComplex.p_descOpcycles]
end LinearStudy
