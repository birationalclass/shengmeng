module
public import Linear.ActualAffineAlgebraDualInternalHomLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
theorem actualModuleFromTildeTopValue (R : CommRingCat.{u}) (P : (Spec R).Modules)
    (x : (modulesSpecToSheaf.obj P).presheaf.obj (op ⊤)) :
    P.fromTildeΓ.app ⊤
      ((tilde.toOpen (R := R) ((modulesSpecToSheaf.obj P).presheaf.obj (op ⊤)) ⊤) x) = x := by
  change (tilde.toOpen (R := R) ((modulesSpecToSheaf.obj P).presheaf.obj (op ⊤)) ⊤ ≫
    (modulesSpecToSheaf.map P.fromTildeΓ).hom.app (op ⊤)) x = x
  erw [Scheme.Modules.toOpen_fromTildeΓ_app]
  change ((modulesSpecToSheaf.obj P).presheaf.map (𝟙 (op ⊤))) x = x
  erw [CategoryTheory.Functor.map_id]
  rfl
attribute [local irreducible] actualAffineAlgebraStructurePushforwardIso
set_option maxHeartbeats 100000 in
theorem actualAffineAlgebraStructurePushforwardIso_element_value
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (b : B) :
    HEq ((actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
      ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤) b))
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  apply heq_of_eq
  simp only [actualAffineAlgebraStructurePushforwardIso, Iso.trans_hom,
    Functor.mapIso_hom, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply]
  have ht :
      ((tilde.functor (CommRingCat.of A)).map
        (restrictedAlgebraModuleEquiv (R := A) (S := B)).toModuleIso.symm.hom).app ⊤
        ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤) b) =
      (tilde.toOpen (R := CommRingCat.of A)
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ⊤) b := by
    exact congr($(tilde.toOpen_map_app (R := CommRingCat.of A)
      (restrictedAlgebraModuleEquiv (R := A) (S := B)).toModuleIso.symm.hom ⊤) b)
  erw [ht]
  simp only [tildePushforwardIso, Iso.trans_hom, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, asIso_hom]
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let P : (Spec (CommRingCat.of A)).Modules :=
    (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde (R := CommRingCat.of B) (ModuleCat.of B B))
  let e := tildePushforwardGlobalIso φ (ModuleCat.of B B)
  have hm : ((tilde.functor (CommRingCat.of A)).map e.inv).app ⊤
      ((tilde.toOpen (R := CommRingCat.of A)
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) ⊤) b) =
    ((tilde.toOpen (R := CommRingCat.of A) (moduleSpecΓFunctor.obj P) ⊤) (e.inv b)) := by
    exact congr($(tilde.toOpen_map_app (R := CommRingCat.of A) e.inv ⊤) b)
  refine (congrArg
    (fun x => (tildeSelf (R := CommRingCat.of B)).hom.app
      (Spec.map φ ⁻¹ᵁ ⊤) (P.fromTildeΓ.app ⊤ x)) hm).trans ?_
  refine (congrArg
    (fun x => (tildeSelf (R := CommRingCat.of B)).hom.app
      (Spec.map φ ⁻¹ᵁ ⊤) x)
    (actualModuleFromTildeTopValue (CommRingCat.of A) P (e.inv b))).trans ?_
  dsimp only [e, tildePushforwardGlobalIso]
  rfl

end LinearStudy
