module
public import Linear.ProjStructureSectionSquare
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R T : Type u} [CommRing K] [CommRing R] [Algebra K R] [CommRing T]
/-- Actual base constants restricted to a positive projective basic open
are the SAME degree-zero chart constants followed by awayToSection. -/
theorem Proj_structure_section_restriction
    (A : ℕ → Submodule K R) [GradedAlgebra A] (c : T →+* A 0)
    {d : ℕ} (a : R) (ha : a ∈ A d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫
      (Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom c)).appTop ≫
      (Proj A).presheaf.map (homOfLE le_top).op =
    CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom A (Submonoid.powers a)).comp c) ≫
      Proj.awayToSection A a := by
  have h := congrArg (fun f => f ≫ (Proj.basicOpenIsoAway A a ha hd).hom)
    (Proj_structure_section_square A c a ha hd)
  have hsigma : (Proj.basicOpenIsoAway A a ha hd).hom = Proj.awayToSection A a := rfl
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at h
  rw [hsigma] at h
  exact h
end LinearStudy
