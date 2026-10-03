module

public import Negativity.RelativeFormalFunctionsMap
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

/-- The actual ideal sheaf of a base point, constructed from its residue
field morphism. For a closed point its support is exactly that singleton. -/
def actualClosedPointIdeal (Y : Scheme.{u}) (y : Y) : Y.IdealSheafData :=
  (Y.fromSpecResidueField y).ker

theorem actual_closed_point_ideal_support (Y : Scheme.{u}) (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    (actualClosedPointIdeal Y y).support = TopologicalSpace.Closeds.mk {y} hy := by
  have : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  ext1
  simp only [actualClosedPointIdeal, Scheme.Hom.support_ker,
    Scheme.range_fromSpecResidueField, hy.closure_eq, TopologicalSpace.Closeds.coe_mk]

/-- The actual closed inverse image is homeomorphic to the actual
scheme-theoretic fiber, without substituting an abstract fiber set. -/
def actualClosedPointFiberHomeomorph {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    ((actualClosedPointIdeal Y y).comap f).subscheme ≃ₜ f.fiber y :=
  (Homeomorph.setCongr (by
    rw [IdealSheafData.support_comap, actual_closed_point_ideal_support Y y hy]
    rfl)).trans (f.fiberHomeo y).symm

theorem actual_closed_point_ideal_top (Y : Scheme.{u}) [IsAffine Y] (y : Y) :
    (actualClosedPointIdeal Y y).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      RingHom.ker (Y.fromSpecResidueField y).appTop.hom := by
  rw [actualClosedPointIdeal, Scheme.ker_of_isAffine]
  simp

theorem actual_closed_point_ideal_top_maximal (Y : Scheme.{u}) [IsAffine Y]
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    ((actualClosedPointIdeal Y y).ideal ⟨⊤, isAffineOpen_top Y⟩).IsMaximal := by
  have : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  let e := Scheme.ΓSpecIso (Y.residueField y)
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  have hf : Function.Surjective (Y.fromSpecResidueField y).appTop := by
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine
      (Y.fromSpecResidueField y)).2
  have hm := RingHom.ker_isMaximal_of_surjective
    (e.hom.hom.comp (Y.fromSpecResidueField y).appTop.hom)
    (he.2.comp hf : Function.Surjective (e.hom.hom.comp
      (Y.fromSpecResidueField y).appTop.hom))
  rw [actual_closed_point_ideal_top]
  simpa only [RingHom.ker_comp_of_injective _ he.1] using hm

/-- Final theorem: over an actual affine Noetherian base, the completion
at the actual ideal of an actual closed point is a local ring. Its ideal
and maximality are derived from genuine residue-field and section maps.
This establishes the completed-ring side of the connectedness argument;
it does not assume or prove the proper formal-functions comparison. -/
theorem actual_closed_point_completion_local (Y : Scheme.{u}) [IsAffine Y]
    [IsLocallyNoetherian Y] (y : Y) (hy : IsClosed ({y} : Set Y)) :
    IsLocalRing (AdicCompletion
      ((actualClosedPointIdeal Y y).ideal ⟨⊤, isAffineOpen_top Y⟩) Γ(Y, ⊤)) := by
  let K := (actualClosedPointIdeal Y y).ideal ⟨⊤, isAffineOpen_top Y⟩
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have : K.IsMaximal := actual_closed_point_ideal_top_maximal Y y hy
  have hfg : K.FG := Ideal.fg_of_isNoetherianRing K
  have hm := AdicCompletion.isMaximal_map_of_le K K (le_refl K) hfg
  have hc := AdicCompletion.isAdicComplete_self K hfg
  exact isLocalRing_of_isAdicComplete_maximal
    (K.map (algebraMap Γ(Y, ⊤) (AdicCompletion K Γ(Y, ⊤))))

end
end Negativity
