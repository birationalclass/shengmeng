module
public import Linear.TildePushforwardUnitValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
attribute [local irreducible] tildePushforwardGlobalIso tildePushforwardIso
/-- The ACTUAL original-element global-section comparison for an ACTUAL
associated-sheaf/pushforward iso. Named to keep deep concrete coefficient
elaboration and kernel checking bounded;no compatibility is assumed. -/
def tildePushforwardOriginalGlobalValue {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)
    (e : tilde N ≅ (Scheme.Modules.pushforward (Spec.map phi)).obj (tilde M))
    (n : N) : (ModuleCat.restrictScalars phi.hom).obj M :=
  (tildePushforwardGlobalIso phi M).hom
    ((moduleSpecΓFunctor (R:=R)).map e.hom ((tilde.adjunction (R:=R)).unit.app N n))
/-- Transport an ACTUAL original module isomorphism through the ACTUAL
tilde-pushforward isomorphism. Every ORIGINAL element retains its value
under the ACTUAL global-section comparison;the square is PROVED. -/
theorem tildePushforwardMappedIso_globalValue {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)
    (e : N ≅ (ModuleCat.restrictScalars phi.hom).obj M) (n : N) :
    (tildePushforwardGlobalIso phi M).hom
      ((moduleSpecΓFunctor (R:=R)).map
        (((tilde.functor R).mapIso e) ≪≫ tildePushforwardIso phi M).hom
          ((tilde.adjunction (R:=R)).unit.app N n))=e.hom n := by
  have hn := congrArg (fun f => f.hom n)
    ((tilde.adjunction (R:=R)).unit.naturality e.hom)
  change (tilde.adjunction (R:=R)).unit.app
      ((ModuleCat.restrictScalars phi.hom).obj M) (e.hom n)=
    (moduleSpecΓFunctor (R:=R)).map ((tilde.functor R).map e.hom)
      ((tilde.adjunction (R:=R)).unit.app N n) at hn
  have hr := tildePushforwardIso_globalValue phi M (e.hom n)
  simp only [Iso.trans_hom,Functor.mapIso_hom,Functor.map_comp,ModuleCat.comp_apply]
  exact (congrArg (fun x => (tildePushforwardGlobalIso phi M).hom
    ((moduleSpecΓFunctor (R:=R)).map (tildePushforwardIso phi M).hom x)) hn.symm).trans hr
/-- The named ACTUAL comparison retains each ORIGINAL element after
mapping the ORIGINAL module iso and applying ACTUAL tilde pushforward. -/
theorem tildePushforwardOriginalGlobalValue_mappedIso {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)
    (e : N ≅ (ModuleCat.restrictScalars phi.hom).obj M) (n : N) :
    tildePushforwardOriginalGlobalValue phi M N
      (((tilde.functor R).mapIso e) ≪≫ tildePushforwardIso phi M) n=e.hom n :=
  tildePushforwardMappedIso_globalValue phi M N e n
/-- Actual associated-sheaf iso from the ORIGINAL base-linear equivalence,
followed by ACTUAL original affine pushforward. -/
def tildePushforwardLinearEquivIso {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)
    (F : N ≃ₗ[R] (ModuleCat.restrictScalars phi.hom).obj M) :
    tilde N ≅ (Scheme.Modules.pushforward (Spec.map phi)).obj (tilde M) :=
  (tilde.functor R).mapIso F.toModuleIso ≪≫ tildePushforwardIso phi M
/-- Keep conversion from linear equivalences to categorical isos inside
the generic proof,so deep concrete native coefficient types need no large
kernel reduction. The original value is EXACTLY F n. -/
theorem tildePushforwardLinearEquivIso_globalValue {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)
    (F : N ≃ₗ[R] (ModuleCat.restrictScalars phi.hom).obj M) (n : N) :
    tildePushforwardOriginalGlobalValue phi M N
      (tildePushforwardLinearEquivIso phi M N F) n=F n :=
  tildePushforwardOriginalGlobalValue_mappedIso phi M N F.toModuleIso n
/-- Prove original-value preservation once at generic native module types.
The predicate may include EVERY original polynomial value and literal
unit trace. No value equality or sheaf iso is assumed in the conclusion. -/
theorem tildePushforward_existsOriginalValues {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)
    (T : Type u) (q : T → N)
    (P : T → (ModuleCat.restrictScalars phi.hom).obj M → Prop)
    (h : ∃ F : N ≃ₗ[R] (ModuleCat.restrictScalars phi.hom).obj M,
      ∀ t,P t (F (q t))) :
    ∃ e : tilde N ≅ (Scheme.Modules.pushforward (Spec.map phi)).obj (tilde M),
      ∀ t,P t (tildePushforwardOriginalGlobalValue phi M N e (q t)) := by
  obtain ⟨F,hF⟩ := h
  refine ⟨tildePushforwardLinearEquivIso phi M N F,?_⟩
  intro t
  rw [tildePushforwardLinearEquivIso_globalValue]
  exact hF t
/-- Preserve two original value families through the actual sheaf comparison.
Keeping the existential and conjunction shape identical avoids opening large
concrete native coefficient terms in specialized kernel proofs. -/
theorem tildePushforward_existsOriginalTwoValues {R S : CommRingCat.{u}}
    (phi : R ⟶ S) (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)
    (T U : Type u) (q : T → N)
    (P : T → U → (ModuleCat.restrictScalars phi.hom).obj M → Prop)
    (P0 : T → (ModuleCat.restrictScalars phi.hom).obj M → Prop)
    (h : ∃ F : N ≃ₗ[R] (ModuleCat.restrictScalars phi.hom).obj M,
      (∀ t v,P t v (F (q t))) ∧ ∀ t,P0 t (F (q t))) :
    ∃ e : tilde N ≅ (Scheme.Modules.pushforward (Spec.map phi)).obj (tilde M),
      (∀ t v,P t v (tildePushforwardOriginalGlobalValue phi M N e (q t))) ∧
      ∀ t,P0 t (tildePushforwardOriginalGlobalValue phi M N e (q t)) := by
  obtain ⟨F,hP,hP0⟩ := h
  refine ⟨tildePushforwardLinearEquivIso phi M N F,?_,?_⟩
  · intro t v
    rw [tildePushforwardLinearEquivIso_globalValue]
    exact hP t v
  · intro t
    rw [tildePushforwardLinearEquivIso_globalValue]
    exact hP0 t
end LinearStudy
