module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The SAME native coextension used by the finite-projection dual is
additive. Its map is postcomposition, so no replacement Hom object is used. -/
theorem nativeCoextensionFunctor_additive (f : R →+* S) :
    (ModuleCat.coextendScalars.{u,u,u} f).Additive := {
  map_add := by
    intro M N g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ell
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro s
    rfl }

attribute [local instance] nativeCoextensionFunctor_additive

/-- Native coextension preserves injective objects by the ACTUAL
restriction/coextension adjunction. Restriction preserves monomorphisms. -/
theorem nativeCoextensionFunctor_preservesInjectiveObjects (f : R →+* S) :
    (ModuleCat.coextendScalars.{u,u,u} f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ModuleCat.restrictCoextendScalarsAdj f)

attribute [local instance] nativeCoextensionFunctor_preservesInjectiveObjects

/-- Each term of the ACTUAL coextended injective resolution is injective
as an S-module. This is derived, not an additional condition on the complex. -/
theorem nativeCoextendedInjectiveResolution_term_injective (f : R →+* S)
    (M : ModuleCat.{u} R) (I : InjectiveResolution M) (n : ℕ) :
    Injective ((((ModuleCat.coextendScalars f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).X n) := by
  change Injective ((ModuleCat.coextendScalars f).obj (I.cocomplex.X n))
  infer_instance

/-- H^0 of the ACTUAL right-derived coextension at any original R-module
is the SAME native coextension. The isomorphism is in ModuleCat S and
therefore retains the source S-action, not just an R-linear comparison. -/
def nativeCoextensionRightDerivedZeroIso (f : R →+* S) (M : ModuleCat.{u} R) :
    ((ModuleCat.coextendScalars f).rightDerived 0).obj M ≅
      (ModuleCat.coextendScalars f).obj M :=
  (ModuleCat.coextendScalars f).rightDerivedZeroIsoSelf.app M

/-- For EVERY actual injective resolution of M, the degree-zero homology
of the SAME coextended cocomplex is isomorphic as an S-module to the
original native coextension. No freeness/CM or duality certificate is supplied. -/
def nativeCoextendedInjectiveResolutionHomologyZeroIso (f : R →+* S)
    (M : ModuleCat.{u} R) (I : InjectiveResolution M) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) 0).obj
      (((ModuleCat.coextendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≅
      (ModuleCat.coextendScalars f).obj M :=
  (I.isoRightDerivedObj (ModuleCat.coextendScalars f) 0).symm ≪≫
    nativeCoextensionRightDerivedZeroIso f M

/-- Any two ACTUAL injective resolutions give homotopy equivalent
native coextended S-module complexes. Thus the derived complex, not
only its degree-zero module, is independent of the resolution choice. -/
def nativeCoextendedInjectiveResolutionHomotopyEquiv (f : R →+* S)
    (M : ModuleCat.{u} R) (I J : InjectiveResolution M) :
    HomotopyEquiv
      (((ModuleCat.coextendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      (((ModuleCat.coextendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex) :=
  (ModuleCat.coextendScalars f).mapHomotopyEquiv (I.homotopyEquiv J)

end LinearStudy
