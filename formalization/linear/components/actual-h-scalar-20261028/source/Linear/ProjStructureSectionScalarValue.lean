module
public import Linear.ProjStructureSectionRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R T : Type u} [CommRing K] [CommRing R] [Algebra K R] [CommRing T]
/-- Pointwise calibration of the ORIGINAL base-global-section scalar
on a genuine positive-degree projective basic open. -/
theorem Proj_structure_section_baseScalar_value
    (A : ℕ → Submodule K R) [GradedAlgebra A] (c : T →+* A 0)
    {d : ℕ} (a : R) (ha : a ∈ A d) (hd : 0 < d)
    (r : Γ(Spec (CommRingCat.of T),⊤)) :
    ((Proj A).presheaf.map (homOfLE le_top).op).hom
      ((Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom c)).appTop.hom r) =
    (Proj.awayToSection A a).hom
      (HomogeneousLocalization.fromZeroRingHom A (Submonoid.powers a)
        (c ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom r))) := by
  have h := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom r))
    (Proj_structure_section_restriction A c a ha hd)
  have hi : (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom r) = r :=
    ConcreteCategory.congr_hom (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of T))) r
  change ((Proj A).presheaf.map (homOfLE le_top).op).hom
      ((Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom c)).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom r))) = _ at h
  rw [hi] at h
  exact h
end LinearStudy
