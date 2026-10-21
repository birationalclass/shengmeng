module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v

/-- Native original module restriction,after forgetting scalars,keeps
EXACT original sections on the image open and all original restrictions. -/
def schemeModuleOpenRestriction_toPresheafIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X ≅
      Scheme.Modules.toPresheaf Y ⋙
        (Functor.whiskeringLeft X.Opensᵒᵖ Y.Opensᵒᵖ AddCommGrpCat.{u}).obj f.opensFunctor.op :=
  Iso.refl _

/-- Actual O-module restriction to an ORIGINAL open immersion preserves
finite limits. The native faithful/limit-reflecting underlying presheaf
functor detects them;the ORIGINAL image-open precomposition preserves them. -/
theorem schemeModuleOpenRestriction_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  let F := Scheme.Modules.restrictFunctor f
  let G := Scheme.Modules.toPresheaf X
  letI : ReflectsLimits G := reflectsLimits_of_reflectsIsomorphisms
  letI : PreservesFiniteLimits (Scheme.Modules.toPresheaf Y) := inferInstance
  letI : PreservesFiniteLimits ((Functor.whiskeringLeft X.Opensᵒᵖ Y.Opensᵒᵖ AddCommGrpCat.{u}).obj f.opensFunctor.op) := inferInstance
  letI : PreservesFiniteLimits (F ⋙ G) :=
    preservesFiniteLimits_of_natIso (schemeModuleOpenRestriction_toPresheafIso f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves F G

/-- Actual original open restriction is additive,without hypotheses on
either coefficient module or the complex. -/
theorem schemeModuleOpenRestriction_additive
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).Additive := by
  letI := schemeModuleOpenRestriction_preservesFiniteLimits f
  exact Functor.additive_of_preserves_binary_products _

/-- Actual original open restriction preserves homology. Use its PROVED
finite-limit preservation and native restriction left adjoint for colimits. -/
theorem schemeModuleOpenRestriction_preservesHomology
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).PreservesHomology := by
  let F := Scheme.Modules.restrictFunctor f
  letI : PreservesFiniteLimits F := schemeModuleOpenRestriction_preservesFiniteLimits f
  letI : F.Additive := schemeModuleOpenRestriction_additive f
  exact ((Functor.exact_tfae F).out 4 3 rfl rfl).mp ⟨inferInstance,inferInstance⟩

/-- The ACTUAL original complex's cohomology sheaf restricts to the ACTUAL
cohomology of its original restricted differential complex. This is a
locality ingredient for gluing the original global Koszul proof,not the
construction of that global complex or its epsilon class. -/
def schemeModuleOpenRestriction_homologyIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {ι : Type v} (c : ComplexShape ι) (K : HomologicalComplex Y.Modules c) (j : ι) :
    (((Scheme.Modules.restrictFunctor f).mapHomologicalComplex c).obj K).homology j ≅
      (Scheme.Modules.restrictFunctor f).obj (K.homology j) := by
  letI := schemeModuleOpenRestriction_additive f
  letI := schemeModuleOpenRestriction_preservesHomology f
  change ((K.sc j).map (Scheme.Modules.restrictFunctor f)).homology ≅ _
  exact (K.sc j).mapHomologyIso (Scheme.Modules.restrictFunctor f)

end LinearStudy
