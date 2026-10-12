module
public import Linear.ActualAffineAlgebraDualEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- On every ORIGINAL algebra element b, the actual affine internal Hom
comparison evaluates the original functional f(b), with actual tilde-toOpen
and structure-pushforward/unit maps. No coordinates are replaced. -/
theorem actualAffineAlgebraDualInternalHomSectionsLinearEquiv_element_evaluation
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (f : B →ₗ[A] A) (b : B) :
    let P := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    let e : tilde (R := CommRingCat.of A) (ModuleCat.of A B) ≅ P := actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)
    let t : tilde (R := CommRingCat.of A) (ModuleCat.of A A) ≅ Q := tildeSelf
    schemeModuleHomSectionEvaluation P Q ⊤
      (actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := A) (B := B) f)
      (e.hom.app ⊤ ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤) b)) =
      t.hom.app ⊤ ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A A) ⊤) (f b)) := by
  dsimp only
  rw [actualAffineAlgebraDualInternalHomSectionsLinearEquiv_evaluation]
  congr 1
  exact congr($(tilde.toOpen_map_app (R := CommRingCat.of A)
    (ModuleCat.ofHom f) ⊤) b)

end LinearStudy
