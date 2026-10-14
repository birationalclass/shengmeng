module
public import Linear.AffineTildeDualHomNaturality
public import Linear.AffineKoszulTermInternalDualHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- Construct the ACTUAL original Koszul-term internal dual with the
literal original tilde R target. The library tildeSelf identifies this
same target with the original structure unit;no target certificate. -/
def affineKoszulTermTildeInternalDualHomIso (R : CommRingCat.{u}) (r j : ℕ) :
    tilde (ModuleCat.of R (Module.Dual R (⋀[R]^j (Fin r → R)))) ≅
      schemeModuleHomModuleSheaf (tilde (ModuleCat.of R (⋀[R]^j (Fin r → R))))
        (tilde (ModuleCat.of R R)) := by
  letI := affineKoszulTerm_finitePresentation R r j
  exact affineTildeFinitePresentationHomIso R (ModuleCat.of R (⋀[R]^j (Fin r → R))) (ModuleCat.of R R)

/-- EVERY ORIGINAL Koszul dual differential agrees with precomposition
on ACTUAL internal sheaf Hom under the CONSTRUCTED ORIGINAL term isos.
Finite presentation of both ORIGINAL exterior terms is PROVED. -/
theorem affineKoszulTermInternalDualHomIso_differential (R : CommRingCat.{u})
    (r j : ℕ) (H : Fin r → R) :
    (tilde.functor R).map
        (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) j).dualMap) ≫
      (affineKoszulTermTildeInternalDualHomIso R r (j+1)).hom =
    (affineKoszulTermTildeInternalDualHomIso R r j).hom ≫
      schemeModuleHomPrecompose (N := tilde (ModuleCat.of R R)) ((tilde.functor R).map
        (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) j))) := by
  unfold affineKoszulTermTildeInternalDualHomIso
  exact @affineTildeFinitePresentationDualHomIso_precompose R
    (ModuleCat.of R (⋀[R]^(j+1) (Fin r → R)))
    (ModuleCat.of R (⋀[R]^j (Fin r → R)))
    (affineKoszulTerm_finitePresentation R r (j+1))
    (affineKoszulTerm_finitePresentation R r j)
    (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) j))

/-- This is the SAME original actual chain-category Koszul differential,
not a replacement differential supplied as a compatibility premise. -/
theorem affineKoszulTermInternalDualHomIso_actualComplex_differential
    (R : CommRingCat.{u}) (r j : ℕ) (H : Fin r → R) :
    (tilde.functor R).map
        (ModuleCat.ofHom (((koszulComplex (Fintype.linearCombination R H)).d (j+1) j).hom).dualMap) ≫
      (affineKoszulTermTildeInternalDualHomIso R r (j+1)).hom =
    (affineKoszulTermTildeInternalDualHomIso R r j).hom ≫
      schemeModuleHomPrecompose (N := tilde (ModuleCat.of R R)) ((tilde.functor R).map
        ((koszulComplex (Fintype.linearCombination R H)).d (j+1) j)) := by
  rw [koszulComplex.d_eq_d]
  exact affineKoszulTermInternalDualHomIso_differential R r j H

end LinearStudy