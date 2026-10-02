module

public import Negativity.CurveImageGeometry
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Closed immersions preserve the actual dimension of point closures. -/
theorem closedImmersion_height_eq {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] (y : Y) : Order.height y = Order.height (j y) := by
  have hsm : StrictMono j := by
    intro a b hab
    refine ⟨j.continuous.specialization_monotone hab.le, ?_⟩
    intro hba
    exact hab.not_ge (j.isEmbedding.isInducing.specializes_iff.mp hba)
  apply Order.height_eq_of_strictMono j hsm
  intro a b hba
  have hb : b ∈ Set.range j := hba.le.mem_closed j.isClosedEmbedding.isClosed_range ⟨a, rfl⟩
  obtain ⟨a', rfl⟩ := hb
  refine ⟨a', ?_, rfl⟩
  refine ⟨j.isEmbedding.isInducing.specializes_iff.mp hba.le, ?_⟩
  intro haa'
  exact hba.not_ge (j.continuous.specialization_monotone haa')

/-- Every actual integral scheme of dimension at most one is either a
single point or has dimension exactly one. -/
theorem integral_scheme_point_or_curve (Y : Scheme.{u}) [IsIntegral Y]
    (hd : Order.krullDim Y ≤ 1) : Subsingleton Y ∨ Order.krullDim Y = 1 := by
  classical
  by_cases hs : Subsingleton Y
  · exact Or.inl hs
  · right
    let : Nontrivial Y := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨y, hy⟩ := exists_ne (genericPoint Y)
    apply le_antisymm hd
    apply Order.one_le_krullDim_iff.mpr
    refine ⟨y, genericPoint Y, ?_⟩
    have hle : y ≤ genericPoint Y := (genericPoint_spec Y).specializes trivial
    refine ⟨hle, ?_⟩
    intro hge
    exact hy (Specializes.antisymm hge hle).eq

/-- Final theorem: the point/curve alternatives for a complete integral
curve's image are derived from its actual scheme-theoretic image. A point
image gives zero actual real Cartier intersection. -/
theorem complete_integral_curve_actual_image_dichotomy
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hdC : Order.krullDim C = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    (f : C ⟶ X) [IsProper (f ≫ b)]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    (Subsingleton f.image ∧
      normalizedRealCartierCurveIntersection hdC k (f ≫ b) f A r = 0) ∨
      Order.krullDim f.image = 1 := by
  have h := complete_integral_curve_actual_image_properties hdC k b f
  have : IsIntegral f.image := h.2.2.1
  rcases integral_scheme_point_or_curve f.image h.2.2.2.2 with hs | hd
  · left
    let := hs
    refine ⟨hs, complete_integral_curve_real_intersection_point_image_zero hdC k (f ≫ b) f ?_ A r⟩
    intro x
    have he := congrArg f.imageι (Subsingleton.elim (f.toImage x) (f.toImage (genericPoint C)))
    simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using he
  · exact Or.inr hd

end
end Negativity
