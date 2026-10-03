module

public import Negativity.HartshorneAffineCover
public import Negativity.HartshorneProjectionFinite
public import Negativity.FiniteProperRelativeProduct
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Final theorem: for an actual proper integral Noetherian scheme over
an actual affine base, construct Hartshorne's actual birational proper
surjective modification with finite map to an actual finite product of
standard relative projective spaces. Affine cover, dimensions, all local
embeddings, common rational map and both graph projections are constructed
internally. Normalizing this modification and constructing the product
Cartier section geometry are subsequent steps of the proper negativity
proof; the complete Chow/projectivity conclusion is not asserted here. -/
theorem exists_actual_hartshorne_finite_modification
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsAffine Y]
    (f : X ⟶ Y) [IsProper f] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (P Z : Scheme.{u})
      (p : P ⟶ Spec (.of Γ(Y, ⊤)))
      (a : ∀ i, P ⟶ Proj
        (MvPolynomial.homogeneousSubmodule (Fin (d i + 1)) Γ(Y, ⊤)))
      (π : Z ⟶ X) (q : Z ⟶ P),
      IsProper p ∧ (∀ i, a i ≫ actualProjectiveSpaceToSpec Γ(Y, ⊤) (d i) = p) ∧
      (∀ (V : ∀ i, (Proj
        (MvPolynomial.homogeneousSubmodule (Fin (d i + 1)) Γ(Y, ⊤))).Opens),
        (∀ i, IsAffineOpen (V i)) → IsAffineOpen (⨅ i, a i ⁻¹ᵁ V i)) ∧
      IsIntegral Z ∧ IsProper π ∧ BirationalMorphism π ∧ Surjective π ∧
      IsFinite q ∧ π ≫ f ≫ Y.toSpecΓ = q ≫ p := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  obtain ⟨ι, hι, U, d, j, W, hcover, hU, hne, hW, hWU, hj, hbase, hproper⟩ :=
    exists_actual_hartshorne_affine_projective_cover f
  letI : Fintype ι := hι
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let V : Fin n → X.Opens := fun i => U (e.symm i)
  let d' : Fin n → ℕ := fun i => d (e.symm i)
  let T : Fin n → Scheme.{u} := fun i => Proj
    (MvPolynomial.homogeneousSubmodule (Fin (d' i + 1)) Γ(Y, ⊤))
  let b : ∀ i, T i ⟶ Spec (.of Γ(Y, ⊤)) := fun i =>
    actualProjectiveSpaceToSpec Γ(Y, ⊤) (d' i)
  let j' : ∀ i, (V i).toScheme ⟶ T i := fun i => j (e.symm i)
  have hV : iSup V = ⊤ := by
    dsimp [V]
    rw [e.symm.surjective.iSup_comp, hcover]
  obtain ⟨P, p, a, hp, ha, hl, _, haff⟩ := exists_actual_finite_proper_relative_product
    (Spec (.of Γ(Y, ⊤))) n T b (fun i => hproper (e.symm i))
  have : IsProper p := hp
  let c : W.toScheme ⟶ Spec (.of Γ(Y, ⊤)) := W.ι ≫ f ≫ Y.toSpecΓ
  let gi : ∀ i, W.toScheme ⟶ T i := fun i =>
    X.homOfLE (hWU (e.symm i)) ≫ j' i
  have hgi : ∀ i, gi i ≫ b i = c := by
    intro i
    dsimp [gi, j', b, T, d', V, c]
    rw [Category.assoc, hbase, ← Category.assoc, Scheme.homOfLE_ι]
  obtain ⟨g, hgp, hga⟩ := hl W.toScheme c gi hgi
  have hj' : ∀ i, IsImmersion (j' i) := fun i => hj (e.symm i)
  have hb : ∀ i, IsSeparated (b i) := by
    intro i
    have : IsProper (b i) := hproper (e.symm i)
    infer_instance
  obtain ⟨Z, π, q, hπ, hbir, hsur, hint, hq, hw⟩ :=
    hartshorne_graph_second_projection_finite (f ≫ Y.toSpecΓ) p V hV T b hb a ha
      j' hj' (fun i => hbase (e.symm i)) W hW
      (fun i => hWU (e.symm i)) g hgp hga
  exact ⟨n, d', P, Z, p, a, π, q, hp, ha, haff inferInstance,
    hint, hπ, hbir, hsur, hq, hw⟩

end
end Negativity
