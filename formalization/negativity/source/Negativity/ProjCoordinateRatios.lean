module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {R : Type u} {σ : Type*} [CommRing R] [SetLike σ R]
  [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The actual homogeneous coordinate ratio a/b in the actual Proj stalk. -/
def projCoordinateRatioStalk {d : ℕ} (a b : 𝒜 d)
    (x : Proj 𝒜) (hb : (b : R) ∉ x.asHomogeneousIdeal) :
    (Proj 𝒜).presheaf.stalk x :=
  (Proj.stalkIso 𝒜 x).inv (HomogeneousLocalization.mk
    ⟨d, a, b, hb⟩)

theorem proj_coordinate_ratio_stalk_unit_iff {d : ℕ} (a b : 𝒜 d)
    (x : Proj 𝒜) (hb : (b : R) ∉ x.asHomogeneousIdeal) :
    IsUnit (projCoordinateRatioStalk 𝒜 a b x hb) ↔
      (a : R) ∉ x.asHomogeneousIdeal := by
  have : IsLocalHom (Proj.stalkIso 𝒜 x).inv.hom := isLocalHom_of_isIso _
  rw [projCoordinateRatioStalk, isUnit_map_iff (Proj.stalkIso 𝒜 x).inv.hom,
    ← HomogeneousLocalization.isUnit_iff_isUnit_val,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

theorem proj_coordinate_ratio_stalk_mul {d : ℕ} (a b c : 𝒜 d)
    (x : Proj 𝒜) (hb : (b : R) ∉ x.asHomogeneousIdeal)
    (hc : (c : R) ∉ x.asHomogeneousIdeal) :
    projCoordinateRatioStalk 𝒜 a b x hb * projCoordinateRatioStalk 𝒜 b c x hc =
      projCoordinateRatioStalk 𝒜 a c x hc := by
  apply (ConcreteCategory.bijective_of_isIso (Proj.stalkIso 𝒜 x).hom).injective
  simp only [projCoordinateRatioStalk, map_mul, Iso.inv_hom_id_apply]
  apply HomogeneousLocalization.val_injective _
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- The actual regular ratio section a/b on the standard Proj open D+(b). -/
def projCoordinateRatioSection {d : ℕ} (a b : 𝒜 d) :
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 (b : R)) :=
  Proj.awayToSection 𝒜 (b : R) (HomogeneousLocalization.mk
    (⟨d, a, b, ⟨1, by simp⟩⟩ : HomogeneousLocalization.NumDenSameDeg 𝒜
      (Submonoid.powers (b : R))))

/-- Final theorem: the actual germ of the coordinate ratio section is its
actual homogeneous-localization stalk ratio. This connects Proj coordinate
charts to genuine Scheme local equations rather than supplied O(1) data. -/
theorem proj_coordinate_ratio_section_germ {d : ℕ} (a b : 𝒜 d)
    (x : Proj 𝒜) (hb : x ∈ Proj.basicOpen 𝒜 b) :
    (Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 b) x hb
      (projCoordinateRatioSection 𝒜 a b) = projCoordinateRatioStalk 𝒜 a b x hb := by
  have he := congrArg (fun m => m (HomogeneousLocalization.mk
    (⟨d, a, b, ⟨1, by simp⟩⟩ : HomogeneousLocalization.NumDenSameDeg 𝒜
      (Submonoid.powers (b : R)))))
    (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (b : R) x hb)
  simp only [ConcreteCategory.comp_apply] at he
  change (Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 (b : R)) x hb
    (projCoordinateRatioSection 𝒜 a b) = (Proj.stalkIso 𝒜 x).inv
    (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hb) _) at he
  rw [he]
  unfold projCoordinateRatioStalk
  apply congrArg (Proj.stalkIso 𝒜 x).inv
  apply HomogeneousLocalization.val_injective _
  simp [HomogeneousLocalization.mapId, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]

end
end Negativity
