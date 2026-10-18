module
public import Linear.KoszulCoordinateWholeNaturality
public import Linear.HomogeneousKoszulCoordinateComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.Exact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {R T : Type u} [CommRing R] [CommRing T]

/-- SAME original coordinate Koszul transported by an ORIGINAL ring
isomorphism,retaining every actual differential and coefficient. -/
def homogeneousKoszulCoordinateRingEquivIso {r : ℕ} (e : R ≃+* T)
    (H : Fin r → R) :
    homogeneousKoszulCoordinateComplex H ≅
      ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (homogeneousKoszulCoordinateComplex (e ∘ H)) := by
  classical
  exact HomologicalComplex.Hom.isoOfComponents
    (fun p =>
      let E : (Set.powersetCard (Fin r) p → R) ≃ₗ[R]
          ((ModuleCat.restrictScalars e.toRingHom).obj
            (ModuleCat.of T (Set.powersetCard (Fin r) p → T))) :=
        { toFun := fun v i => e (v i)
          invFun := fun v i => e.symm (v i)
          left_inv := fun v => by funext i; exact e.symm_apply_apply (v i)
          right_inv := fun v => by funext i; exact e.apply_symm_apply (v i)
          map_add' := fun v w => by funext i; exact e.map_add (v i) (w i)
          map_smul' := fun c v => by funext i; exact e.map_mul c (v i) }
      E.toModuleIso) (by
        intro i j hij
        simp only [ComplexShape.down_Rel] at hij
        subst hij
        simp only [Functor.mapHomologicalComplex_obj_d,homogeneousKoszulCoordinateComplex,
          ChainComplex.of_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change homogeneousKoszulCoordinateDifferential (e ∘ H) j (fun i => e (x i)) =
          (fun i => e (homogeneousKoszulCoordinateDifferential H j x i))
        exact (homogeneousKoszulCoordinateDifferential_map e.toRingHom H j x).symm)

/-- Exactness transports through the SAME ring equivalence and actual
coordinate Koszul comparison,using exactness of the ACTUAL source complex. -/
theorem homogeneousKoszulCoordinate_exactAt_ringEquiv {r : ℕ}
    (e : R ≃+* T) (H : Fin r → R) (j : ℕ)
    (h : (homogeneousKoszulCoordinateComplex H).ExactAt j) :
    (homogeneousKoszulCoordinateComplex (e ∘ H)).ExactAt j := by
  let F := ModuleCat.restrictScalars e.toRingHom
  have hF := h.of_iso (homogeneousKoszulCoordinateRingEquivIso e H)
  change (((homogeneousKoszulCoordinateComplex (e ∘ H)).sc j).map F).Exact at hF
  change ((homogeneousKoszulCoordinateComplex (e ∘ H)).sc j).Exact
  exact (((homogeneousKoszulCoordinateComplex (e ∘ H)).sc j).exact_map_iff_of_faithful F).mp hF

/-- Exactness of the ACTUAL native exterior Koszul transfers to the SAME
original forms under a ring isomorphism,using the actual canonical bases. -/
theorem functionKoszul_exactAt_ringEquiv {r : ℕ}
    (e : R ≃+* T) (H : Fin r → R) (j : ℕ)
    (h : (koszulComplex (Fintype.linearCombination R H)).ExactAt j) :
    (koszulComplex (Fintype.linearCombination T (e ∘ H))).ExactAt j := by
  have hc := h.of_iso (homogeneousKoszulCoordinateComplexIso H)
  have ht := homogeneousKoszulCoordinate_exactAt_ringEquiv e H j hc
  exact ht.of_iso (homogeneousKoszulCoordinateComplexIso (e ∘ H)).symm

end LinearStudy
