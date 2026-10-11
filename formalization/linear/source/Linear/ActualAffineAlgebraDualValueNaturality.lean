module
public import Linear.ActualAffineAlgebraDualSpecValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- Actual affine internal-Hom values transport by the genuine structure
sheaf map whenever the specified algebra functionals transport their values.
The latter equation is separately derived for the original weighted dual. -/
theorem actualAffineAlgebraDualInternalHomSectionsLinearEquiv_value_naturality
    {A B T C : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing C]
    [Algebra A B] [Algebra T C]
    (φ : A →+* T) (γ : B →+* C) (f : B →ₗ[A] A) (g : C →ₗ[T] T)
    (hf : ∀ b, g (γ b) = φ (f b)) (b : B) :
    let PA := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let QA : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    let PT := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap T C)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of C)).ringCatSheaf)
    let QT : (Spec (CommRingCat.of T)).Modules := SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf
    let eA : tilde (R := CommRingCat.of A) (ModuleCat.of A B) ≅ PA := actualAffineAlgebraStructurePushforwardIso
    let eT : tilde (R := CommRingCat.of T) (ModuleCat.of T C) ≅ PT := actualAffineAlgebraStructurePushforwardIso
    schemeModuleHomSectionEvaluation PT QT ⊤
      (actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := T) (B := C) g)
      (eT.hom.app ⊤ ((tilde.toOpen (R := CommRingCat.of T) (ModuleCat.of T C) ⊤) (γ b))) =
    (Spec.map (CommRingCat.ofHom φ)).appTop
      (schemeModuleHomSectionEvaluation PA QA ⊤
        (actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := A) (B := B) f)
        (eA.hom.app ⊤ ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤) b))) := by
  dsimp only
  rw [actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value,
    actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value, hf]
  exact congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) (f b))

end LinearStudy
