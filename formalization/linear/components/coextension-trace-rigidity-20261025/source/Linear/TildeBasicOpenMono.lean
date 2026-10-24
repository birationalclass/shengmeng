module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- The actual associated-sheaf map on a basic open is the unique localized
map determined by the original module map, not an assumed model. -/
theorem tilde_basicOpen_map_eq_localized (f : M ⟶ N) (a : R) :
    ((modulesSpecToSheaf.map (tilde.map f)).1.app (.op (PrimeSpectrum.basicOpen a))).hom=
      IsLocalizedModule.map (Submonoid.powers a)
        (tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom
        (tilde.toOpen N (PrimeSpectrum.basicOpen a)).hom f.hom := by
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers a)
    (tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom
    (tilde.toOpen N (PrimeSpectrum.basicOpen a)).hom
  exact (ModuleCat.hom_ext_iff.mp
    (tilde.toOpen_map_app f (PrimeSpectrum.basicOpen a))).trans
      (IsLocalizedModule.map_comp (Submonoid.powers a)
        (tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom
        (tilde.toOpen N (PrimeSpectrum.basicOpen a)).hom f.hom).symm

/-- Actual injectivity of the associated-sheaf map on every basic open. -/
theorem tilde_basicOpen_map_injective (f : M ⟶ N) (hf : Function.Injective f.hom) (a : R) :
    Function.Injective
      ((modulesSpecToSheaf.map (tilde.map f)).1.app (.op (PrimeSpectrum.basicOpen a))).hom := by
  rw [tilde_basicOpen_map_eq_localized]
  exact IsLocalizedModule.map_injective _ _ _ f.hom hf

end LinearStudy
