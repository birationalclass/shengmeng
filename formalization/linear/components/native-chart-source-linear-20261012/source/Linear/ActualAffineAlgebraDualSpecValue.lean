module
public import Linear.ActualAffineAlgebraDualElementEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- The actual associated module's scalar section is the original
structure-sheaf section specified by mathlib's Gamma-Spec isomorphism. -/
theorem actualTildeSelf_toOpen_top_value (A : Type u) [CommRing A] (a : A) :
    (tildeSelf (R := CommRingCat.of A)).hom.app ⊤
      ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A A) ⊤) a) =
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv a := by
  rfl

/-- The original functional's algebra value is exactly the value of its
actual internal-Hom section, via the actual structure-sheaf section map. -/
theorem actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (f : B →ₗ[A] A) (b : B) :
    let P := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    let e : tilde (R := CommRingCat.of A) (ModuleCat.of A B) ≅ P := actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)
    schemeModuleHomSectionEvaluation P Q ⊤
      (actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := A) (B := B) f)
      (e.hom.app ⊤ ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤) b)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (f b) := by
  dsimp only
  rw [actualAffineAlgebraDualInternalHomSectionsLinearEquiv_element_evaluation]
  exact actualTildeSelf_toOpen_top_value A (f b)

end LinearStudy
