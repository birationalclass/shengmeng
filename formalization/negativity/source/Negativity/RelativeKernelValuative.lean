module

public import Negativity.RelativeKernelFiltration
public import Negativity.FiniteNormalGeometry
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Properness extends the inverse on the actual birational open along
every valuation ring with dominant generic map. The top map of the
valuative square is constructed internally from that inverse. -/
theorem actual_proper_birational_valuation_lift
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (V K : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (b : Spec (.of V) ⟶ Y)
    [IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ b)] :
    ∃ l : Spec (.of V) ⟶ X, l ≫ f = b := by
  let β := Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ b
  obtain ⟨U, hU, hIso⟩ := hf
  have : IsIso (f ∣_ U) := hIso
  have hβU : Set.range β ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hz : z = genericPoint (Spec (.of K)) := Subsingleton.elim _ _
    rw [hz, dominant_genericPoint_eq β]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
      (by simpa using hU)
  let βU := IsOpenImmersion.lift U.ι β hβU
  let a := βU ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have ha : a ≫ f = β := by
    dsimp [a]
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι,
      IsIso.inv_hom_id_assoc]
    exact IsOpenImmersion.lift_fac _ _ hβU
  have hp : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓
      @LocallyOfFiniteType) f := by
    rw [← IsProper.eq_valuativeCriterion]
    exact inferInstance
  let square : ValuativeCommSq f :=
    { R := V, K := K, i₁ := a, i₂ := b, commSq := ⟨ha⟩ }
  obtain ⟨l⟩ := ((ValuativeCriterion.existence hp.1.1.1) square).exists_lift
  exact ⟨l.l, l.fac_right⟩

/-- Final theorem: every actual kernel-ideal element stays in the
corresponding extended ideal power in every valuation ring dominating the
generic base map. Proper birationality supplies the actual lift; ideal
membership follows from the actual scheme pullback/pushforward Galois
connection and affine coordinate compatibility. No integral-closure or
uniform-filtration assertion is assumed. -/
theorem actual_relative_kernel_valuative_contraction
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (I : Y.IdealSheafData) (n : ℕ)
    (V K : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (b : Spec (.of V) ⟶ Y)
    [IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ b)] :
    (actualRelativeKernelIdeal f I n).map b.appTop.hom ≤
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ n).map b.appTop.hom := by
  obtain ⟨l, hl⟩ := actual_proper_birational_valuation_lift f hf V K b
  have hh : (((I ^ n).comap f).map f).comap b ≤ (I ^ n).comap b := by
    rw [← hl, IdealSheafData.comap_comp, IdealSheafData.comap_comp]
    exact IdealSheafData.comap_mono l
      (IdealSheafData.comap_map_le ((I ^ n).comap f) f)
  have he := hh ⟨⊤, isAffineOpen_top (Spec (.of V))⟩
  rw [actual_affine_ideal_pullback, actual_affine_ideal_pullback] at he
  exact he

end
end Negativity
