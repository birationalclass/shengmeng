/-
Adapted from CBirkbeck/AINTLIB, commit ab1451487da02cd4483d0e2cdb2cc9e44bbbac17,
ModularCurves/ForMathlib/SchemeModuleSheaf.lean. Apache License 2.0.
This minimal extraction uses the pinned mathlib's actual module/additive sheaves.
-/
module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u v u1 u2 u3 v1 v2 v3

/-- The ACTUAL additive sheaf underlying an O_X-module, with source category
explicitly X.Modules. This matches the upstream scheme-module functor. -/
def schemeModuleToAdditiveSheaf (X : AlgebraicGeometry.Scheme.{u}) :
    X.Modules ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf.{u} X.ringCatSheaf

/-- The actual underlying-additive functor preserves finite limits. -/
@[instance]
theorem schemeModuleToAdditiveSheaf_preservesFiniteLimits
    (X : AlgebraicGeometry.Scheme.{u}) :
    PreservesFiniteLimits (schemeModuleToAdditiveSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

/-- Colimit preservation descends from a reflector composition.
This is the narrow categorical step reused by the actual additive sheaf functor. -/
theorem moduleAdditiveSheaf_preservesColimitsOfShape_of_reflector_comp
    {C : Type u1} [Category.{v1} C] {D : Type u2} [Category.{v2} D]
    {E : Type u3} [Category.{v3} E] (R : C ⥤ D) [Reflective R]
    {J : Type u} [Category.{v} J] (F : C ⥤ E)
    [PreservesColimitsOfShape J ((reflector R) ⋙ F)] [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  refine @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _
    (NatIso.hcomp (asIso (𝟙 K)) (asIso (reflectorAdjunction R).counit).symm).symm
      ⟨fun hc => ⟨?_⟩⟩
  let hc2 := colimit.isColimit (K ⋙ R)
  let psi := IsColimit.uniqueUpToIso (isColimitOfPreserves (reflector R) hc2) hc
  have phi := IsColimit.ofIsoColimit (isColimitOfPreserves (reflector R ⋙ F) hc2)
    (Functor.mapCoconeMapCocone (H := reflector R) (H' := F)
      (colimit.cocone (K ⋙ R))).symm
  exact IsColimit.ofIsoColimit phi ((Cocone.functoriality _ F).mapIso psi)

/-- The same reflector argument for all colimits of a specified size. -/
theorem moduleAdditiveSheaf_preservesColimitsOfSize_of_reflector_comp
    {C : Type u1} [Category.{v1} C] {D : Type u2} [Category.{v2} D]
    {E : Type u3} [Category.{v3} E] (R : C ⥤ D) [Reflective R]
    (F : C ⥤ E) [PreservesColimitsOfSize.{v, u} ((reflector R) ⋙ F)]
    [HasColimitsOfSize.{v, u} D] : PreservesColimitsOfSize.{v, u} F where
  preservesColimitsOfShape := moduleAdditiveSheaf_preservesColimitsOfShape_of_reflector_comp R F

/-- The ACTUAL functor forgetting a scheme-module sheaf to its additive sheaf
preserves colimits. No exactness or section-lifting certificate is assumed. -/
theorem schemeModuleAdditiveSheaf_preservesColimitsOfSize
    (X : AlgebraicGeometry.Scheme.{u}) :
    PreservesColimitsOfSize.{v, u} (schemeModuleToAdditiveSheaf X) := by
  letI : Reflective (AlgebraicGeometry.Scheme.Modules.toPresheafOfModules X) :=
    { L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
      adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj) }
  have : PreservesColimitsOfSize.{v, u}
      (reflector (AlgebraicGeometry.Scheme.Modules.toPresheafOfModules X) ⋙
        schemeModuleToAdditiveSheaf X) :=
    comp_preservesColimits (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat)
  exact moduleAdditiveSheaf_preservesColimitsOfSize_of_reflector_comp
    (AlgebraicGeometry.Scheme.Modules.toPresheafOfModules X)
    (schemeModuleToAdditiveSheaf X)

/-- The actual additive-sheaf functor sends the zero module map to zero. -/
@[instance]
theorem schemeModuleAdditiveSheaf_preservesZeroMorphisms
    (X : AlgebraicGeometry.Scheme.{u}) :
    (schemeModuleToAdditiveSheaf X).PreservesZeroMorphisms where
  map_zero := by intros; rfl

/-- An ACTUAL short exact sequence of O_X-module sheaves becomes an ACTUAL
short exact sequence of additive sheaves. This derives the comparison needed
by the H1-to-section-lifting step, rather than assuming it as a certificate. -/
theorem schemeModuleShortExact_underlyingAdditiveSheaf
    {X : AlgebraicGeometry.Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) :
    (S.map (schemeModuleToAdditiveSheaf X)).ShortExact := by
  letI : PreservesColimitsOfSize.{u, u} (schemeModuleToAdditiveSheaf X) :=
    schemeModuleAdditiveSheaf_preservesColimitsOfSize X
  letI : PreservesFiniteColimits (schemeModuleToAdditiveSheaf X) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact hS.map_of_exact _
end LinearStudy
