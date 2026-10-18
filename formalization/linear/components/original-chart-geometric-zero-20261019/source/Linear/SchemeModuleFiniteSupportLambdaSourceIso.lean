module
public import Linear.SchemeModuleClosedDiscreteGlobalToInternalExtSections
public import Linear.SchemeModuleGlobalToInternalExtSourceNaturality
public import Linear.SchemeModuleFiniteFreeFrameInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
/-- Transfer bijectivity of the SAME canonical lambda along an ACTUAL source-module isomorphism, using the previously proved source-naturality square. -/
theorem schemeModuleGlobalToInternalExt_bijective_of_sourceIso {X : Scheme.{u}}
    {P Q : X.Modules} (e : P ≅ Q) (N : X.Modules) (n : ℕ)
    (hQ : Function.Bijective (schemeModuleGlobalToInternalExt Q N n)) :
    Function.Bijective (schemeModuleGlobalToInternalExt P N n) := by
  let A : Ext.{u} Q N (n+1) → Ext.{u} P N (n+1) :=
    fun x => (Ext.mk₀ e.hom).comp x (zero_add _)
  let B : (SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleInternalExt Q N (n+1)) →
      (SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleInternalExt P N (n+1)) :=
    fun x => x ≫ schemeModuleInternalExtSourceMap e.hom N (n+1)
  have hA : Function.Bijective A :=
    (((extFunctor (C := X.Modules) (n+1)).mapIso e.op).app N).addCommGroupIsoToAddEquiv.bijective
  have hB : Function.Bijective B := by
    simpa [B,Iso.homCongr,schemeModuleInternalExtSourceIso] using
      (Iso.homCongr (Iso.refl (SheafOfModules.unit X.ringCatSheaf))
        (schemeModuleInternalExtSourceIso e N (n+1)).symm).bijective
  apply (Function.Bijective.of_comp_iff (schemeModuleGlobalToInternalExt P N n) hA).mp
  have hs : (schemeModuleGlobalToInternalExt P N n) ∘ A =
      B ∘ (schemeModuleGlobalToInternalExt Q N n) := by
    funext x
    exact schemeModuleGlobalToInternalExt_sourceNaturality e.hom n x
  rw [hs]
  exact hB.comp hQ
/-- An actual source iso to a closed discrete direct image supplies the geometric source bridge; no lambda/Ext iso is an extra input. -/
theorem schemeModuleGlobalToInternalExt_closedDiscrete_bijective_of_sourceIso
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (L : D.Modules) {P : X.Modules} (e : P ≅ (Scheme.Modules.pushforward f).obj L)
    (N : X.Modules) (n : ℕ) :
    Function.Bijective (schemeModuleGlobalToInternalExt P N n) :=
  schemeModuleGlobalToInternalExt_bijective_of_sourceIso e N n
    (schemeModuleGlobalToInternalExt_closedDiscrete_bijective f hf L N n)
/-- Actual source identification with a sheaf on the original Artinian closed cut transfers the canonical comparison. -/
theorem schemeModuleGlobalToInternalExt_artinianClosed_bijective_of_sourceIso
    {D X : Scheme.{u}} [IsArtinianScheme D] (f : D ⟶ X) [IsClosedImmersion f]
    (L : D.Modules) {P : X.Modules} (e : P ≅ (Scheme.Modules.pushforward f).obj L)
    (N : X.Modules) (n : ℕ) :
    Function.Bijective (schemeModuleGlobalToInternalExt P N n) :=
  schemeModuleGlobalToInternalExt_closedDiscrete_bijective_of_sourceIso f
    f.isClosedEmbedding.isClosedMap L e N n
end LinearStudy
