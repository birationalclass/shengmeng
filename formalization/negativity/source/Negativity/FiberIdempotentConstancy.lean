module

public import Negativity.ProperBirationalSections
public import Negativity.LocalConnectedness
public import Negativity.SchemeClopenIdempotent
public import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

def actualFiberConstantMap {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    Y.residueField y →+* Γ(f.fiber y, ⊤) :=
  (f.fiberToSpecResidueField y).appTop.hom.comp
    (Scheme.ΓSpecIso (Y.residueField y)).inv.hom

theorem actual_proper_birational_fiber_lift_is_constant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) (y : Y)
    (s : Γ(X, ⊤)) :
    ∃ c : Y.residueField y, actualFiberConstantMap f y c = (f.fiberι y).appTop s := by
  obtain ⟨r, hr⟩ := (proper_normal_birational_open_functions_bijective f hf hnY ⊤).2 s
  let t := (Y.fromSpecResidueField y).appTop r
  let c := (Scheme.ΓSpecIso (Y.residueField y)).hom t
  refine ⟨c, ?_⟩
  have h := congrArg (fun g : f.fiber y ⟶ Y => g.appTop r) (f.fiber_fac y)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  calc
    actualFiberConstantMap f y c = (f.fiberToSpecResidueField y).appTop t := by
      simp [actualFiberConstantMap, c]
    _ = (f.fiberι y).appTop (f.appTop r) := h.symm
    _ = (f.fiberι y).appTop s := congrArg (f.fiberι y).appTop hr

def actualFiberToNeighborhood {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (y : Y) (hy : y ∈ U) : f.fiber y ⟶ (f ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (f.fiberι y) (by
    rintro x ⟨t, rfl⟩
    have hx : f (f.fiberι y t) = y := by
      have h := f.range_fiberι y
      have hm : f.fiberι y t ∈ Set.range (f.fiberι y) := ⟨t, rfl⟩
      rw [h] at hm
      exact hm
    exact ⟨⟨f.fiberι y t, by change f (f.fiberι y t) ∈ U; rwa [hx]⟩, rfl⟩)

def actualResidueToNeighborhood {Y : Scheme.{u}} (U : Y.Opens)
    (y : Y) (hy : y ∈ U) : Spec (Y.residueField y) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (Y.fromSpecResidueField y) (by
    rintro x ⟨t, rfl⟩
    have hx : Y.fromSpecResidueField y t = y := by
      have hm : Y.fromSpecResidueField y t ∈ Set.range (Y.fromSpecResidueField y) := ⟨t, rfl⟩
      rw [Y.range_fromSpecResidueField y] at hm
      exact hm
    exact ⟨⟨Y.fromSpecResidueField y t, by rwa [hx]⟩, rfl⟩)

theorem actual_fiber_neighborhood_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (y : Y) (hy : y ∈ U) :
    actualFiberToNeighborhood f U y hy ≫ f ∣_ U =
      f.fiberToSpecResidueField y ≫ actualResidueToNeighborhood U y hy := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι,
    actualFiberToNeighborhood, actualResidueToNeighborhood,
    IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac_assoc]
  exact f.fiber_fac y

def actualNeighborhoodToFiberSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (y : Y) (hy : y ∈ U) :
    Γ(X, f ⁻¹ᵁ U) →+* Γ(f.fiber y, ⊤) :=
  (actualFiberToNeighborhood f U y hy).appTop.hom.comp (f ⁻¹ᵁ U).topIso.inv.hom

theorem actual_proper_birational_neighborhood_lift_is_constant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (y : Y) (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)) :
    ∃ c : Y.residueField y, actualFiberConstantMap f y c =
      actualNeighborhoodToFiberSections f U y hy s := by
  obtain ⟨r, hr⟩ := (proper_normal_birational_open_functions_bijective f hf hnY U).2 s
  let t := (actualResidueToNeighborhood U y hy).appTop (U.topIso.inv r)
  let c := (Scheme.ΓSpecIso (Y.residueField y)).hom t
  have hrest : (f ∣_ U).appTop (U.topIso.inv r) = (f ⁻¹ᵁ U).topIso.inv s := by
    have h := f.resLE_app_top (U := U) (V := f ⁻¹ᵁ U) le_rfl
    rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at h
    have hmap : (f ∣_ U).appTop = U.topIso.hom ≫ f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := h
    calc
      _ = (U.topIso.hom ≫ f.app U ≫ (f ⁻¹ᵁ U).topIso.inv) (U.topIso.inv r) :=
        congrArg (fun g : Γ(U.toScheme, ⊤) ⟶ Γ((f ⁻¹ᵁ U).toScheme, ⊤) => g (U.topIso.inv r)) hmap
      _ = _ := by
        change (f ⁻¹ᵁ U).topIso.inv (f.app U (U.topIso.hom (U.topIso.inv r))) =
          (f ⁻¹ᵁ U).topIso.inv s
        rw [Iso.inv_hom_id_apply, hr]
  have h := congrArg (fun g : f.fiber y ⟶ U.toScheme => g.appTop (U.topIso.inv r))
    (actual_fiber_neighborhood_square f U y hy)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  refine ⟨c, ?_⟩
  calc
    actualFiberConstantMap f y c = (f.fiberToSpecResidueField y).appTop t := by
      simp [actualFiberConstantMap, c]
    _ = (actualFiberToNeighborhood f U y hy).appTop ((f ∣_ U).appTop (U.topIso.inv r)) := h.symm
    _ = actualNeighborhoodToFiberSections f U y hy s := by
      rw [hrest]; rfl

/-- Final theorem: any idempotent on an actual nonempty fiber that
extends to an actual neighborhood-source section is trivial for a proper
birational map to a normal base. The lift itself is not assumed to be
idempotent: its restriction is a residue-field constant, and only that
constant is proved idempotent. Existence of the lift remains separate. -/
theorem actual_proper_birational_fiber_lifted_idempotent_trivial
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (y : Y) [Nonempty (f.fiber y)] (e : Γ(f.fiber y, ⊤)) (he : e * e = e)
    (hlift : ∃ (U : Y.Opens) (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)),
      actualNeighborhoodToFiberSections f U y hy s = e) : e = 0 ∨ e = 1 := by
  have : Nonempty (⊤ : (f.fiber y).Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty (f.fiber y)), trivial⟩⟩
  have : Nontrivial Γ(f.fiber y, ⊤) := (f.fiber y).component_nontrivial ⊤
  obtain ⟨U, hy, s, hs⟩ := hlift
  obtain ⟨c, hc⟩ := actual_proper_birational_neighborhood_lift_is_constant f hf hnY U y hy s
  have hce : actualFiberConstantMap f y c = e := hc.trans hs
  have hcinj : Function.Injective (actualFiberConstantMap f y) :=
    RingHom.injective (actualFiberConstantMap f y)
  have hcid : c * c = c := by
    apply hcinj
    rw [map_mul, hce, he]
  rcases localRing_idempotent_trivial (Y.residueField y) c hcid with h0 | h1
  · left
    rw [← hce, h0, map_zero]
  · right
    rw [← hce, h1, map_one]

end
end Negativity
