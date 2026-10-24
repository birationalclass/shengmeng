module
-- Proposed actual image-support bridge;verification evidence is recorded separately.
public import Linear.DiscreteSchemePushforwardOpenProjector
public import Linear.SchemeModuleInternalExtOpenSupport
public import Linear.SchemeModuleOpenRestrictionExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Proposed bridge:actual original open restriction carries the image
of a locally zero source map to zero. Use existing original exactness and
native image epi/mono factorization,not a new image comparison premise. -/
theorem schemeModuleImage_open_isZero_of_map_zero
    {X : Scheme.{u}} {A B : X.Modules} (b : A ⟶ B) (V : X.Opens)
    (hb : (Scheme.Modules.restrictFunctor V.ι).map b=0) :
    IsZero ((Abelian.image b).restrict V.ι) := by
  let F := Scheme.Modules.restrictFunctor V.ι
  letI : PreservesFiniteLimits F := schemeModuleOpenRestriction_preservesFiniteLimits V.ι
  letI : F.Additive := schemeModuleOpenRestriction_additive V.ι
  have hi : F.map (Abelian.image.ι b)=0 := by
    apply (cancel_epi (F.map (Abelian.factorThruImage b))).1
    rw [← Functor.map_comp,Abelian.image.fac,hb,comp_zero]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono (F.map (Abelian.image.ι b))).1
  simp only [Category.id_comp,zero_comp,hi]
/-- Proposed bridge:the ACTUAL constructed source projector restricts
to zero outside its actual selected inverse-image component. -/
theorem discreteSchemePushforwardOpenProjector_restrict_zero
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (L : D.Modules)
    (U : D.Opens) (V : X.Opens)
    (h : f ⁻¹ᵁ V ≤ (show D.Opens from ⟨(U : Set D)ᶜ,isOpen_discrete _⟩)) :
    (Scheme.Modules.restrictFunctor V.ι).map (discreteSchemePushforwardOpenProjector f L U)=0 := by
  apply SheafOfModules.hom_ext
  ext T s
  let O : X.Opens := V.ι ''ᵁ T.unop
  have hOV : O ≤ V := by
    rintro x ⟨y,hy,rfl⟩
    exact y.property
  change (discreteSchemePushforwardOpenProjector f L U).app O s=0
  apply discreteSchemePushforwardOpenProjector_app_zero
  intro x hx
  exact h (hOV hx)
/-- Proposed bridge:actual image source has proved support bound. -/
theorem discreteSchemePushforwardOpenProjector_image_restrict_isZero
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (L : D.Modules)
    (U : D.Opens) (V : X.Opens)
    (h : f ⁻¹ᵁ V ≤ (show D.Opens from ⟨(U : Set D)ᶜ,isOpen_discrete _⟩)) :
    IsZero ((Abelian.image (discreteSchemePushforwardOpenProjector f L U)).restrict V.ι) :=
  schemeModuleImage_open_isZero_of_map_zero _ V
    (discreteSchemePushforwardOpenProjector_restrict_zero f L U V h)
/-- Proposed bridge:all ACTUAL internal SHEAF Ext of that constructed
image source vanish off the selected component,for ALL coefficients and
ALL degrees. Local trace nonzero weights are still a separate obligation. -/
theorem discreteSchemePushforwardOpenProjector_image_internalExt_restrict_isZero
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (L : D.Modules)
    (U : D.Opens) (V : X.Opens)
    (h : f ⁻¹ᵁ V ≤ (show D.Opens from ⟨(U : Set D)ᶜ,isOpen_discrete _⟩))
    (N : X.Modules) (q : ℕ) :
    IsZero ((schemeModuleInternalExt (Abelian.image (discreteSchemePushforwardOpenProjector f L U)) N q).restrict V.ι) :=
  schemeModuleInternalExt_open_isZero_of_source V.ι _ N
    (discreteSchemePushforwardOpenProjector_image_restrict_isZero f L U V h) q
end LinearStudy
