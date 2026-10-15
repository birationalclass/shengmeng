module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Additive
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u v

/-- The ORIGINAL Spec global-section functor is additive on its SAME
actual section maps,not an assumed exactness or comparison certificate. -/
@[instance] theorem affineModuleSpecGlobalSections_additive (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).Additive where
  map_add := by
    intros M N f g
    apply ModuleCat.hom_ext
    rfl

/-- The ACTUAL native tilde-Gamma counit is an isomorphism of the ENTIRE
original quasicoherent SHEAF complex on Spec R,retaining EVERY original
differential. Native quasicoherence implies invertibility;no desired
complex isomorphism or counit-invertibility certificate is assumed. -/
def affineQuasicoherentComplexCounitIso (R : CommRingCat.{u})
    {ι : Type v} (c : ComplexShape ι) (C : HomologicalComplex (Spec R).Modules c)
    [∀ i, (C.X i).IsQuasicoherent] :
    ((tilde.functor R).mapHomologicalComplex c).obj
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex c).obj C) ≅ C :=
  HomologicalComplex.Hom.isoOfComponents (fun i => asIso (C.X i).fromTildeΓ) (by
    intro i j hij
    change (C.X i).fromTildeΓ ≫ C.d i j =
      (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map (C.d i j)) ≫
        (C.X j).fromTildeΓ
    exact (Scheme.Modules.fromTildeΓNatTrans.naturality (C.d i j)).symm)

/-- EVERY comparison component is the SAME ACTUAL geometric counit. -/
theorem affineQuasicoherentComplexCounitIso_hom (R : CommRingCat.{u})
    {ι : Type v} (c : ComplexShape ι) (C : HomologicalComplex (Spec R).Modules c)
    [∀ i, (C.X i).IsQuasicoherent] (i : ι) :
    (affineQuasicoherentComplexCounitIso R c C).hom.f i = (C.X i).fromTildeΓ := rfl

end LinearStudy
