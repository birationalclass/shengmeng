module

public import Negativity.SchemeClopenIdempotent
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual structure sheaf glues the characteristic section of any
actual clopen set. Its actual germs are 1 on the set and 0 off the set. -/
theorem actual_clopen_characteristic_exists_unique (X : Scheme.{u})
    (S : Set X) (hS : IsClopen S) :
    ∃! a : Γ(X, ⊤), ∀ x : X,
      X.presheaf.Γgerm x a = if x ∈ S then 1 else 0 := by
  classical
  let U : X.Opens := ⟨S, hS.isOpen⟩
  let V : X.Opens := ⟨Sᶜ, hS.isClosed.isOpen_compl⟩
  have hdisj : U ⊓ V = ⊥ := by ext x; change (x ∈ S ∧ x ∈ Sᶜ) ↔ False; simp
  have hcover : U ⊔ V = ⊤ := by
    ext x
    change (x ∈ S ∨ x ∈ Sᶜ) ↔ True
    exact iff_true_intro (em (x ∈ S))
  let ee : Γ(X, U ⊔ V) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) :=
    (X.sheaf.isProductOfDisjoint U V hdisj).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  let b : Γ(X, U ⊔ V) := ee.inv (1, 0)
  have hbU : X.presheaf.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op b = 1 := by
    have h := IsLimit.conePointUniqueUpToIso_inv_comp
      (X.sheaf.isProductOfDisjoint U V hdisj)
      (CommRingCat.prodFanIsLimit _ _) ⟨WalkingPair.left⟩
    exact congrArg (fun m => m (1, 0)) h
  have hbV : X.presheaf.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op b = 0 := by
    have h := IsLimit.conePointUniqueUpToIso_inv_comp
      (X.sheaf.isProductOfDisjoint U V hdisj)
      (CommRingCat.prodFanIsLimit _ _) ⟨WalkingPair.right⟩
    exact congrArg (fun m => m (1, 0)) h
  let a : Γ(X, ⊤) := X.presheaf.map (eqToHom hcover.symm).op b
  have ha (x : X) : X.presheaf.Γgerm x a = if x ∈ S then 1 else 0 := by
    have hx : x ∈ U ⊔ V := by rw [hcover]; trivial
    change X.presheaf.germ ⊤ x trivial a = _
    rw [X.presheaf.germ_res_apply (eqToHom hcover.symm) x trivial b]
    by_cases hxS : x ∈ S
    · rw [if_pos hxS, ← X.presheaf.germ_res_apply
        (homOfLE le_sup_left : U ⟶ U ⊔ V) x hxS b, hbU]
      exact map_one _
    · rw [if_neg hxS, ← X.presheaf.germ_res_apply
        (homOfLE le_sup_right : V ⟶ U ⊔ V) x hxS b, hbV]
      exact map_zero _
  refine ⟨a, ha, ?_⟩
  intro c hc
  exact TopCat.Presheaf.section_ext X.sheaf ⊤ c a
    (fun x _ => (hc x).trans (ha x).symm)

/-- The actual characteristic regular function, with no arbitrary
idempotent choice or disconnectedness hypothesis. -/
def actualClopenCharacteristic (X : Scheme.{u}) (S : Set X) (hS : IsClopen S) : Γ(X, ⊤) :=
  (actual_clopen_characteristic_exists_unique X S hS).exists.choose

theorem actual_clopen_characteristic_germ (X : Scheme.{u}) (S : Set X)
    (hS : IsClopen S) (x : X) :
    X.presheaf.Γgerm x (actualClopenCharacteristic X S hS) =
      if x ∈ S then 1 else 0 :=
  (actual_clopen_characteristic_exists_unique X S hS).exists.choose_spec x

theorem actual_clopen_characteristic_idempotent (X : Scheme.{u}) (S : Set X)
    (hS : IsClopen S) :
    actualClopenCharacteristic X S hS * actualClopenCharacteristic X S hS =
      actualClopenCharacteristic X S hS := by
  classical
  apply TopCat.Presheaf.section_ext X.sheaf ⊤
  intro x _
  change X.presheaf.Γgerm x
    (actualClopenCharacteristic X S hS * actualClopenCharacteristic X S hS) =
      X.presheaf.Γgerm x (actualClopenCharacteristic X S hS)
  simp only [map_mul, actual_clopen_characteristic_germ]
  split <;> simp

/-- Final theorem: genuine pullback of regular functions preserves the
actual characteristic sections of clopen decompositions. In particular
this supplies compatibility along actual infinitesimal-thickening maps;
no compatibility equation is taken as an input. -/
theorem actual_clopen_characteristic_pullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) (S : Set Y) (hS : IsClopen S) :
    f.appTop (actualClopenCharacteristic Y S hS) =
      actualClopenCharacteristic X (f ⁻¹' S) (hS.preimage f.continuous) := by
  classical
  apply TopCat.Presheaf.section_ext X.sheaf ⊤
  intro x _
  change X.presheaf.Γgerm x (f.appTop (actualClopenCharacteristic Y S hS)) =
    X.presheaf.Γgerm x (actualClopenCharacteristic X (f ⁻¹' S) _)
  calc
    _ = f.stalkMap x (Y.presheaf.Γgerm (f x) (actualClopenCharacteristic Y S hS)) :=
      (f.germ_stalkMap_apply ⊤ x trivial _).symm
    _ = _ := by
      simp only [actual_clopen_characteristic_germ]
      by_cases hx : f x ∈ S <;> simp [hx]

end
end Negativity
