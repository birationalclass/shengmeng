module

public import Negativity.FiniteCurvePoints
public import Mathlib.Topology.KrullDimension
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Coheight zero on an actual integral Scheme is exactly its generic point. -/
theorem curve_coheight_zero_generic (C : Scheme.{u}) [IsIntegral C]
    (x : C) (hx : Order.coheight x = 0) : x = genericPoint C := by
  have hm := Order.coheight_eq_zero.mp hx
  have hxg : x ≤ genericPoint C := (genericPoint_spec C).specializes trivial
  have hgx : genericPoint C ≤ x := hm hxg
  exact (Specializes.antisymm hgx hxg).eq

theorem curve_nonGeneric_coheight_one (C : Scheme.{u}) [IsIntegral C]
    (hd : Order.krullDim C ≤ 1) (x : C) (hx : x ≠ genericPoint C) :
    Order.coheight x = 1 := by
  have hle : Order.coheight x ≤ 1 := WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim x).trans hd)
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr fun hz => hx (curve_coheight_zero_generic C x hz))

theorem curve_genericPoint_not_closed (C : Scheme.{u}) [IsIntegral C]
    (hd : Order.krullDim C = 1) : ¬ IsClosed ({genericPoint C} : Set C) := by
  intro hc
  obtain ⟨x, hx⟩ := curve_exists_coheight_one C hd
  have he : x = genericPoint C := Set.mem_singleton_iff.mp
    (hc.closure_eq ▸ ((genericPoint_spec C).specializes trivial).mem_closure)
  have hm : IsMax (genericPoint C) := fun y _ => (genericPoint_spec C).specializes trivial
  have hzero := Order.coheight_eq_zero.mpr hm
  rw [he, hzero] at hx
  norm_num at hx

/-- Actual fibers of a proper dominant map between integral curves are
finite: a nongeneric fiber is a proper closed subset, and the generic fiber
cannot contain a closed point because proper maps closed points to closed points. -/
theorem proper_dominant_curve_fibers_finite {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (hdX : Order.krullDim X ≤ 1) (hdY : Order.krullDim Y = 1) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  by_cases hy : y = genericPoint Y
  · apply Set.finite_singleton (genericPoint X) |>.subset
    intro x hx
    apply Set.mem_singleton_iff.mpr
    by_contra hng
    have hxc := curve_nonGeneric_coheight_one X hdX x hng
    have hc := f.isClosedMap _ (curve_coheight_one_isClosed X hdX x hxc)
    rw [Set.image_singleton] at hc
    have he : f x = genericPoint Y := (Set.mem_singleton_iff.mp hx).trans hy
    exact curve_genericPoint_not_closed Y hdY (he ▸ hc)
  · have hcy := curve_coheight_one_isClosed Y hdY.le y
      (curve_nonGeneric_coheight_one Y hdY.le y hy)
    have hp : IsClosed (f ⁻¹' {y}) := hcy.preimage f.continuous
    have : QuasiSober (f ⁻¹' {y}) := hp.isClosedEmbedding_subtypeVal.quasiSober
    have hproper : closure (f ⁻¹' {y}) ≠ Set.univ := by
      rw [hp.closure_eq]
      intro he
      have hη : genericPoint X ∈ f ⁻¹' {y} := he.symm ▸ Set.mem_univ _
      have heq := Set.mem_singleton_iff.mp hη
      rw [dominant_genericPoint_eq f] at heq
      exact hy heq.symm
    apply (NoetherianSpace.finite_coheight_one_of_closure_ne_univ hproper).subset
    intro x hx
    refine ⟨hx, curve_nonGeneric_coheight_one X hdX x ?_⟩
    intro he
    have heq := Set.mem_singleton_iff.mp hx
    rw [he, dominant_genericPoint_eq f] at heq
    exact hy heq.symm

/-- Final theorem: an actual proper dominant morphism of integral
Noetherian curves is finite. The locally-quasi-finite input is derived from
actual finite fibers and Zariski's main theorem. No normality or
separability hypothesis is needed for this finiteness step. -/
theorem proper_dominant_integral_curve_isFinite {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (hdX : Order.krullDim X = 1) (hdY : Order.krullDim Y = 1) : IsFinite f := by
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    (proper_dominant_curve_fibers_finite f hdX.le hdY)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end Negativity
