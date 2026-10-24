module
public import Linear.SchemeModuleAdditiveSheafColimits
public import Mathlib.Topology.Sheaves.Abelian
import all Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v

/-- Exactness of an ACTUAL original O_X-module short complex can be
checked on its ACTUAL underlying additive stalks. Native sheaf stalk
criterion and the existing exact faithful forgetful functor are reused. -/
theorem schemeModuleShortComplex_exact_iff_actualAdditiveStalks
    {X : Scheme.{u}} (S : ShortComplex X.Modules) :
    letI : (TopCat.Sheaf.forget AddCommGrpCat.{u} X).Additive :=
      TopCat.Sheaf.instAdditivePresheafForget (C := AddCommGrpCat.{u}) (X := X)
    letI (x : X) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive :=
      TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) x
    letI := schemeModuleAdditiveSheaf_preservesZeroMorphisms X
    S.Exact ↔ ∀ x : X,
      (S.map (schemeModuleToAdditiveSheaf X ⋙
        TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact := by
  letI : (TopCat.Sheaf.forget AddCommGrpCat.{u} X).Additive :=
    TopCat.Sheaf.instAdditivePresheafForget (C := AddCommGrpCat.{u}) (X := X)
  letI (x : X) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) x
  letI := schemeModuleAdditiveSheaf_preservesZeroMorphisms X
  let F := schemeModuleToAdditiveSheaf X
  letI : F.Faithful :=
    inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Faithful
  letI : PreservesColimitsOfSize.{u,u} F := schemeModuleAdditiveSheaf_preservesColimitsOfSize X
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits _
  have h := (S.exact_map_iff_of_faithful F).symm.trans
    (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map F))
  simpa only [ShortComplex.map_comp] using h

/-- The SAME actual sheaf-module complex is exact in a degree iff its
ACTUAL additive-stalk complexes are exact there. No desired global
exactness,local cover,quasicoherence or coefficient condition is assumed. -/
theorem schemeModuleComplex_exactAt_iff_actualAdditiveStalks
    {X : Scheme.{u}} {ι : Type v} {c : ComplexShape ι}
    (C : HomologicalComplex X.Modules c) (i : ι) :
    letI : (TopCat.Sheaf.forget AddCommGrpCat.{u} X).Additive :=
      TopCat.Sheaf.instAdditivePresheafForget (C := AddCommGrpCat.{u}) (X := X)
    letI (x : X) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive :=
      TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) x
    letI := schemeModuleAdditiveSheaf_preservesZeroMorphisms X
    C.ExactAt i ↔ ∀ x : X,
      (((schemeModuleToAdditiveSheaf X ⋙
        TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex c).obj C).ExactAt i := by
  letI : (TopCat.Sheaf.forget AddCommGrpCat.{u} X).Additive :=
    TopCat.Sheaf.instAdditivePresheafForget (C := AddCommGrpCat.{u}) (X := X)
  letI (x : X) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) x
  letI := schemeModuleAdditiveSheaf_preservesZeroMorphisms X
  change (C.sc i).Exact ↔ ∀ x : X,
    ((C.sc i).map (schemeModuleToAdditiveSheaf X ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact
  exact schemeModuleShortComplex_exact_iff_actualAdditiveStalks (C.sc i)

end LinearStudy
