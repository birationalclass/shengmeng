module
public import Linear.ProjStructureSectionScalarValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R T : Type u} [CommRing K] [CommRing R] [Algebra K R] [CommRing T]
/-- The ORIGINAL structure-map scalar restricted to the ORIGINAL basic
open, with its section-ring type fixed before module elaboration. -/
def projBasicOpenBaseScalar (A : ℕ → Submodule K R) [GradedAlgebra A]
    (c : T →+* A 0) (a : R) (r : Γ(Spec (CommRingCat.of T),⊤)) :
    (ProjectiveSpectrum.Proj.structureSheaf A).1.obj (op (Proj.basicOpen A a)) :=
  ((Proj A).presheaf.map (homOfLE le_top).op).hom
    ((Proj.toSpecZero A ≫ Spec.map (CommRingCat.ofHom c)).appTop.hom r)
/-- Exact calibration with the original homogeneous-localization constants;
the scalar was defined by restriction, not by this chart formula. -/
theorem projBasicOpenBaseScalar_eq_chart
    (A : ℕ → Submodule K R) [GradedAlgebra A] (c : T →+* A 0)
    {d : ℕ} (a : R) (ha : a ∈ A d) (hd : 0 < d)
    (r : Γ(Spec (CommRingCat.of T),⊤)) :
    projBasicOpenBaseScalar A c a r =
      (Proj.awayToSection A a).hom
        (HomogeneousLocalization.fromZeroRingHom A (Submonoid.powers a)
          (c ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom r))) :=
  Proj_structure_section_baseScalar_value A c a ha hd r
end LinearStudy
