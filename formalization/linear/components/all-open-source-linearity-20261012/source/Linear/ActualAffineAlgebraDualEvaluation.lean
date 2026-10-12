module
public import Linear.ActualAffineAlgebraDualInternalHomValues
public import Linear.SchemeModuleHomEvaluationRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- Actual internal Hom evaluation on the whole scheme is the app of
the same global module morphism, without replacing either section map. -/
theorem schemeModuleHomSectionEvaluation_top_value
    {X : Scheme.{u}} (M N : X.Modules)
    (f : Γ(schemeModuleHomModuleSheaf M N,⊤)) (x : Γ(M,⊤)) :
    schemeModuleHomSectionEvaluation M N ⊤ f x =
      (schemeModuleHomTopSectionsEquiv M N f).app ⊤ x := by
  rfl

/-- The actual affine Hom comparison evaluates the original associated
module section by the actual tilde map of the original algebra functional. -/
theorem actualAffineAlgebraDualInternalHomSectionsLinearEquiv_evaluation
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (f : B →ₗ[A] A) (x : Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A B),⊤)) :
    let P := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    let e : tilde (R := CommRingCat.of A) (ModuleCat.of A B) ≅ P := actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)
    let t : tilde (R := CommRingCat.of A) (ModuleCat.of A A) ≅ Q := tildeSelf
    schemeModuleHomSectionEvaluation P Q ⊤
      (actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := A) (B := B) f)
      (e.hom.app ⊤ x) =
      t.hom.app ⊤
        (((tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f)).app ⊤ x) := by
  dsimp only
  rw [schemeModuleHomSectionEvaluation_top_value,
    actualAffineAlgebraDualInternalHomSectionsLinearEquiv_value]
  have H := (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom_inv_id
  have hx := congrArg (fun h => h.app ⊤ x) H
  dsimp at hx ⊢
  rw [hx]
  rfl

end LinearStudy
