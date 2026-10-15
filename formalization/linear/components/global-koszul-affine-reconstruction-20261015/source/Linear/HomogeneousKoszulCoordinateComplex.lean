module
public import Linear.KoszulHomogeneousCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {S : Type u} [CommRing S]

/-- SAME original Koszul complex in its canonical exterior coordinates. -/
def homogeneousKoszulCoordinateComplex {r : ℕ} (H : Fin r → S) :
    ChainComplex (ModuleCat.{u} S) ℕ :=
  ChainComplex.of (fun p => ModuleCat.of S (Set.powersetCard (Fin r) p → S))
    (fun p => ModuleCat.ofHom (homogeneousKoszulCoordinateDifferential H p))
    (fun p => by
      rw [← ModuleCat.ofHom_comp, homogeneousKoszulCoordinateDifferential_comp,
        ModuleCat.ofHom_zero])

/-- The ORIGINAL exterior complex and the coordinate complex are
isomorphic by the ORIGINAL canonical bases, commuting with EVERY differential. -/
def homogeneousKoszulCoordinateComplexIso {r : ℕ} (H : Fin r → S) :
    koszulComplex (Fintype.linearCombination S H) ≅ homogeneousKoszulCoordinateComplex H :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (koszulExteriorCoordinates (S := S) r p).toModuleIso) (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      subst hij
      simp only [homogeneousKoszulCoordinateComplex, koszulComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      symm
      change koszulExteriorCoordinates (S := S) r j
        (koszulComplex.d (Fintype.linearCombination S H) j x) =
          koszulExteriorCoordinates (S := S) r j
            (koszulComplex.d (Fintype.linearCombination S H) j
              ((koszulExteriorCoordinates (S := S) r (j+1)).symm
                (koszulExteriorCoordinates (S := S) r (j+1) x)))
      rw [LinearEquiv.symm_apply_apply])

/-- The comparison map is the ORIGINAL canonical coordinate map in every degree. -/
theorem homogeneousKoszulCoordinateComplexIso_hom {r : ℕ} (H : Fin r → S) (p : ℕ) :
    (homogeneousKoszulCoordinateComplexIso H).hom.f p =
      ModuleCat.ofHom (koszulExteriorCoordinates (S := S) r p).toLinearMap := rfl

end LinearStudy
