module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Negativity.AffineProductCharts
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: construct the actual finite relative product of proper
schemes over an actual base. Actual projections and their lifting property
are constructed by repeated genuine scheme fiber products. In particular,
a compatible family of rational maps has an actual common target map. -/
theorem exists_actual_finite_proper_relative_product
    (S : Scheme.{u}) (n : ℕ) (T : Fin n → Scheme.{u})
    (b : ∀ i, T i ⟶ S) (hb : ∀ i, IsProper (b i)) :
    ∃ (P : Scheme.{u}) (p : P ⟶ S) (a : ∀ i, P ⟶ T i),
      IsProper p ∧ (∀ i, a i ≫ b i = p) ∧
      (∀ (Q : Scheme.{u}) (c : Q ⟶ S) (g : ∀ i, Q ⟶ T i)
        (hg : ∀ i, g i ≫ b i = c),
        ∃ l : Q ⟶ P, l ≫ p = c ∧ ∀ i, l ≫ a i = g i) ∧
      (∀ (Q : Scheme.{u}) (l₁ l₂ : Q ⟶ P),
        l₁ ≫ p = l₂ ≫ p → (∀ i, l₁ ≫ a i = l₂ ≫ a i) → l₁ = l₂) ∧
      (IsAffine S → ∀ (V : ∀ i, (T i).Opens),
        (∀ i, IsAffineOpen (V i)) → IsAffineOpen (⨅ i, a i ⁻¹ᵁ V i)) := by
  induction n with
  | zero =>
    refine ⟨S, 𝟙 S, (fun i => Fin.elim0 i), inferInstance, (fun i => Fin.elim0 i), ?_, ?_, ?_⟩
    · intro Q c g hg
      exact ⟨c, by simp, fun i => Fin.elim0 i⟩
    · intro Q l₁ l₂ h _
      simpa using h
    · intro hS V _
      have : IsAffine S := hS
      simpa using (isAffineOpen_top S)
  | succ n ih =>
    obtain ⟨P', p', a', hp', ha', hl', hext', haff'⟩ := ih
      (fun i => T i.succ) (fun i => b i.succ) (fun i => hb i.succ)
    have : IsProper p' := hp'
    have : IsProper (b 0) := hb 0
    let P := pullback (b 0) p'
    let p : P ⟶ S := pullback.snd (b 0) p' ≫ p'
    let a : ∀ i, P ⟶ T i := Fin.cases (pullback.fst (b 0) p')
      (fun i => pullback.snd (b 0) p' ≫ a' i)
    have ha : ∀ i, a i ≫ b i = p := by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact pullback.condition
      · simp [a, p, ha']
    refine ⟨P, p, a, by dsimp [p]; infer_instance, ha, ?_, ?_, ?_⟩
    · intro Q c g hg
      obtain ⟨l', hlp, hla⟩ := hl' Q c (fun i => g i.succ) (fun i => hg i.succ)
      let l : Q ⟶ P := pullback.lift (g 0) l' ((hg 0).trans hlp.symm)
      refine ⟨l, by simp [l, p, hlp], ?_⟩
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [l, a]
      · simp [l, a, hla]
    · intro Q l₁ l₂ hp he
      apply pullback.hom_ext
      · exact he 0
      · apply hext' Q (l₁ ≫ pullback.snd (b 0) p') (l₂ ≫ pullback.snd (b 0) p')
        · simpa [p, Category.assoc] using hp
        · intro i
          simpa [a, Category.assoc] using he i.succ
    · intro hS V hV
      have : IsAffine S := hS
      have heq : (⨅ i, a i ⁻¹ᵁ V i) =
          pullback.fst (b 0) p' ⁻¹ᵁ V 0 ⊓
            pullback.snd (b 0) p' ⁻¹ᵁ (⨅ i, a' i ⁻¹ᵁ V i.succ) := by
        apply TopologicalSpace.Opens.ext
        ext x
        simp only [TopologicalSpace.Opens.coe_iInf, TopologicalSpace.Opens.coe_inf,
          Scheme.Hom.coe_preimage, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter]
        change (∀ i, a i x ∈ V i) ↔
          pullback.fst (b 0) p' x ∈ V 0 ∧
          ∀ i, a' i (pullback.snd (b 0) p' x) ∈ V i.succ
        simpa [a, Scheme.Hom.comp_apply] using
          (Fin.forall_fin_succ (P := fun i => a i x ∈ V i))
      rw [heq]
      exact actual_affine_product_chart (b 0) p' (V 0) (hV 0)
        (⨅ i, a' i ⁻¹ᵁ V i.succ) (haff' hS (fun i => V i.succ) (fun i => hV i.succ))

end
end Negativity
