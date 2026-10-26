module
public import Linear.AffineTildeFinitePresentationHomIso
public import Linear.SchemeModuleHomPrecomposeComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable (R : CommRingCat.{u}) (M' M N : ModuleCat.{u} R)

/-- ACTUAL original top Hom-section evaluation preserves precomposition
by the SAME original tilde f and SAME original source section x. -/
theorem affineTildeHomTopSection_precompose_evaluation (f : M' ⟶ M)
    (h : Γ(schemeModuleHomModuleSheaf (tilde M) (tilde N),⊤)) (x : Γ(tilde M',⊤)) :
    affineQuasicoherentHomActualOpenSectionsLinearEquiv (tilde N) (tilde M') ⊤
      ((schemeModuleHomPrecompose ((tilde.functor R).map f)).app ⊤ h) x =
    affineQuasicoherentHomActualOpenSectionsLinearEquiv (tilde N) (tilde M) ⊤ h
      (((tilde.functor R).map f).app ⊤ x) := by
  rw [affineQuasicoherentHomActualOpenSectionsLinearEquiv_evaluation,
    affineQuasicoherentHomActualOpenSectionsLinearEquiv_evaluation]
  have hi : (⊤ : (Spec R).Opens).leTop.op=𝟙 (op (⊤ : (Spec R).Opens)) := Subsingleton.elim _ _
  rw [hi]
  simp only [CategoryTheory.Functor.map_id]
  rfl

/-- ACTUAL original global-Hom identification preserves the ORIGINAL
R-linear precomposition phi o f. Both original tilde source-section
maps are related using the library ACTUAL tilde unit naturality. -/
theorem affineTildeHomTopLinearEquiv_precompose (f : M' ⟶ M)
    (h : Γ(schemeModuleHomModuleSheaf (tilde M) (tilde N),⊤)) :
    affineTildeHomTopLinearEquiv R M' N
      ((schemeModuleHomPrecompose ((tilde.functor R).map f)).app ⊤ h) =
      (affineTildeHomTopLinearEquiv R M N h).comp f.hom := by
  apply LinearMap.ext
  intro x
  change (tilde.isoTop N).toLinearEquiv.symm
      (affineQuasicoherentHomActualOpenSectionsLinearEquiv (tilde N) (tilde M') ⊤
        ((schemeModuleHomPrecompose ((tilde.functor R).map f)).app ⊤ h)
        ((tilde.isoTop M').toLinearEquiv x)) =
    (tilde.isoTop N).toLinearEquiv.symm
      (affineQuasicoherentHomActualOpenSectionsLinearEquiv (tilde N) (tilde M) ⊤ h
        ((tilde.isoTop M).toLinearEquiv (f.hom x)))
  congr 1
  rw [affineTildeHomTopSection_precompose_evaluation]
  congr 1
  exact (congrArg (fun g => g.hom x) ((tilde.adjunction (R := R)).unit.naturality f)).symm

end LinearStudy
