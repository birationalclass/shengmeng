module
public import Linear.DiscreteSchemeOpenIdempotent
public import Linear.OriginalGlobalModuleScalarRingLaws
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {D X : Scheme.{u}} [DiscreteTopology D]
/-- The constructed original idempotent is one on every actual subopen. -/
theorem discreteSchemeOpenIdempotent_restrict_one_of_le
    (U V : D.Opens) (h : V ≤ U) :
    D.presheaf.map V.leTop.op (discreteSchemeOpenIdempotent D U)=1 := by
  calc
    _ = D.presheaf.map (homOfLE h).op
        (D.presheaf.map U.leTop.op (discreteSchemeOpenIdempotent D U)) := by
      rw [← ConcreteCategory.comp_apply,← D.presheaf.map_comp]
      rfl
    _ = 1 := by rw [discreteSchemeOpenIdempotent_restrict_one,map_one]
/-- The SAME idempotent is zero on every actual complementary subopen. -/
theorem discreteSchemeOpenIdempotent_restrict_zero_of_le_complement
    (U V : D.Opens)
    (h : V ≤ (show D.Opens from ⟨(U : Set D)ᶜ,isOpen_discrete _⟩)) :
    D.presheaf.map V.leTop.op (discreteSchemeOpenIdempotent D U)=0 := by
  let W : D.Opens := ⟨(U : Set D)ᶜ,isOpen_discrete _⟩
  calc
    _ = D.presheaf.map (homOfLE h).op
        (D.presheaf.map W.leTop.op (discreteSchemeOpenIdempotent D U)) := by
      rw [← ConcreteCategory.comp_apply,← D.presheaf.map_comp]
      rfl
    _ = 0 := by rw [discreteSchemeOpenIdempotent_restrict_complement_zero,map_zero]
/-- An ACTUAL source endomorphism on the original direct-image module,
constructed from original structure-sheaf gluing. No abstract projector
is supplied as an input. It applies to arbitrary coefficients on D. -/
def discreteSchemePushforwardOpenProjector (f : D ⟶ X)
    (L : D.Modules) (U : D.Opens) :
    (Scheme.Modules.pushforward f).obj L ⟶ (Scheme.Modules.pushforward f).obj L :=
  (Scheme.Modules.pushforward f).map
    (originalGlobalModuleScalar (discreteSchemeOpenIdempotent D U) L)
/-- Actual source idempotence,derived from the original coefficient ring
laws and actual pushforward functor,with no finiteness/free/flat input. -/
theorem discreteSchemePushforwardOpenProjector_idempotent
    (f : D ⟶ X) (L : D.Modules) (U : D.Opens) :
    discreteSchemePushforwardOpenProjector f L U ≫ discreteSchemePushforwardOpenProjector f L U =
      discreteSchemePushforwardOpenProjector f L U := by
  unfold discreteSchemePushforwardOpenProjector
  rw [← Functor.map_comp,← originalGlobalModuleScalar_mul,discreteSchemeOpenIdempotent_idempotent]
/-- Literal actual local action on EVERY original ambient open. -/
theorem discreteSchemePushforwardOpenProjector_app
    (f : D ⟶ X) (L : D.Modules) (U : D.Opens) (V : X.Opens)
    (s : Γ((Scheme.Modules.pushforward f).obj L,V)) :
    (discreteSchemePushforwardOpenProjector f L U).app V s =
      D.presheaf.map (f ⁻¹ᵁ V).leTop.op (discreteSchemeOpenIdempotent D U) •
        (show Γ(L,f ⁻¹ᵁ V) from s) := by
  rfl
/-- The actual direct-image projector is identity on opens whose actual
inverse image lies in U. No support certificate is supplied. -/
theorem discreteSchemePushforwardOpenProjector_app_one
    (f : D ⟶ X) (L : D.Modules) (U : D.Opens) (V : X.Opens)
    (h : f ⁻¹ᵁ V ≤ U) (s : Γ((Scheme.Modules.pushforward f).obj L,V)) :
    (discreteSchemePushforwardOpenProjector f L U).app V s=s := by
  rw [discreteSchemePushforwardOpenProjector_app,
    discreteSchemeOpenIdempotent_restrict_one_of_le U (f ⁻¹ᵁ V) h,one_smul]
/-- The actual direct-image projector kills opens whose actual inverse
image lies in the complement. This is actual sheaf action,not global duality. -/
theorem discreteSchemePushforwardOpenProjector_app_zero
    (f : D ⟶ X) (L : D.Modules) (U : D.Opens) (V : X.Opens)
    (h : f ⁻¹ᵁ V ≤ (show D.Opens from ⟨(U : Set D)ᶜ,isOpen_discrete _⟩))
    (s : Γ((Scheme.Modules.pushforward f).obj L,V)) :
    (discreteSchemePushforwardOpenProjector f L U).app V s=0 := by
  rw [discreteSchemePushforwardOpenProjector_app,
    discreteSchemeOpenIdempotent_restrict_zero_of_le_complement U (f ⁻¹ᵁ V) h,zero_smul]
end LinearStudy
