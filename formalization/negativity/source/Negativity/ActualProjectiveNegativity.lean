module

public import Negativity.ActualProjectiveAffineNegativity
public import Negativity.ActualOpenPushforward
public import Negativity.ActualOpenNef
public import Negativity.RelativeProjectiveEmbedding
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Final theorem: actual real-Cartier negativity (1) on a general normal
base. Projectivity is specified by genuine relative projective closed
embeddings over actual affine base opens. All restrictions, fixed Cartier
pullbacks, pushforward coefficient comparisons, nef transport, O(1)
section construction, exceptional E and actual-curve contradictions are
proved internally. No affine-base, E, section, numerical intersection,
geometric comparison or local effectivity input is assumed. Arbitrary
characteristic and arbitrary finite real Cartier presentations remain. -/
theorem actual_projective_negativity_part_one
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hproj : ActualLocallyProjective f)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (d : τ → ℝ)
    (hpush : CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
      (∑ t, (A t).weightedWeilCycle hnX (d t))))
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -d t)) :
    ∀ x : X, 0 ≤ ∑ t, d t * ((A t).coefficient hnX x : ℝ) := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := f x) (U := (⊤ : Y.Opens)) (by trivial)
  have : Nonempty U := ⟨⟨f x, hxU⟩⟩
  have : IsAffine U.toScheme := hU
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hxU⟩⟩
  let : IsDominant (f ⁻¹ᵁ U).ι := Opens.isDominant_ι
    ((f ⁻¹ᵁ U).isOpen.dense (by simpa using ‹Nonempty (f ⁻¹ᵁ U)›))
  let hnV := normalStalks_restrict X (f ⁻¹ᵁ U) hnX
  let hnU := normalStalks_restrict Y U hnY
  let AA (t : τ) := actualCartierPullback (f ⁻¹ᵁ U).ι (A t)
  have hp := actual_real_cartier_pushforward_effective_on_open hnX hnY f hf U A d hpush
  have hn := actual_relative_nef_on_target_open k b f U A (fun t => -d t) hnef
  have : CompactSpace (f ⁻¹ᵁ U).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ U)
  obtain ⟨P⟩ := hproj U hU ‹Nonempty U›
  have := P.closed
  have hall := actual_projective_affine_negativity k (U.ι ≫ b) (f ∣_ U)
    (birationalMorphism_restrict f hf U) hnV hnU AA d hp hn
    P.dimension P.embedding
  have hlocal := hall (⟨x, hxU⟩ : (f ⁻¹ᵁ U).toScheme)
  simpa only [AA, actual_cartier_open_restriction_coefficient hnX (f ⁻¹ᵁ U),
    Scheme.Opens.ι_apply] using hlocal

end
end Negativity
