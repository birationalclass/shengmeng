module
public import Linear.ProjectiveResolutionNativeHomCocycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u
variable {R : Type u} [CommRing R] {X : ModuleCat.{u} R}

/-- CONSTRUCT original native cycle/boundary quotient equivalence with
ACTUAL DERIVED MODULE Ext from PROVED boundary kernel and surjectivity.
SAME actual projective resolution is retained;N arbitrary. -/
def projectiveResolutionNativeHomPositiveCohomologyQuotientEquiv
    (P : ProjectiveResolution X) (N : ModuleCat.{u} R) (n : ℕ) :
    (((P.complex.linearYonedaObj R N).sc' n (n+1) (n+2)).moduleCatLeftHomologyData.H) ≃ₗ[R]
      CategoryTheory.Abelian.Ext.{u} X N (n+1) :=
  (Submodule.quotEquivOfEq _ _
    (projectiveResolutionNativeHomCycleExtLinearMap_kernel P N n).symm).trans
      ((projectiveResolutionNativeHomCycleExtLinearMap P N (n+1)).quotKerEquivOfSurjective
        (projectiveResolutionNativeHomCycleExtLinearMap_surjective P N (n+1)))

/-- Every positive degree of the ACTUAL original native Hom cochain
complex computes ACTUAL derived MODULE Ext,using native homology.
No desired Ext/cohomology equivalence or coefficient condition is input. -/
def projectiveResolutionNativeHomPositiveCohomologyIso
    (P : ProjectiveResolution X) (N : ModuleCat.{u} R) (n : ℕ) :
    (P.complex.linearYonedaObj R N).homology (n+1) ≅
      ModuleCat.of R (CategoryTheory.Abelian.Ext.{u} X N (n+1)) :=
  (P.complex.linearYonedaObj R N).homologyIsoSc' n (n+1) (n+2)
    ((ComplexShape.up ℕ).prev_eq' (by rfl)) ((ComplexShape.up ℕ).next_eq' (by rfl)) ≪≫
      ((P.complex.linearYonedaObj R N).sc' n (n+1) (n+2)).moduleCatHomologyIso ≪≫
        (projectiveResolutionNativeHomPositiveCohomologyQuotientEquiv P N n).toModuleIso

/-- SAME actual cohomology class map is SAME original resolution's
actual extMk representative morphism on original native cycles. -/
theorem projectiveResolutionNativeHomPositiveCohomologyIso_classMap
    (P : ProjectiveResolution X) (N : ModuleCat.{u} R) (n : ℕ) :
    (P.complex.linearYonedaObj R N).homologyπ (n+1) ≫
      (projectiveResolutionNativeHomPositiveCohomologyIso P N n).hom =
    ((P.complex.linearYonedaObj R N).cyclesIsoSc' n (n+1) (n+2)
        ((ComplexShape.up ℕ).prev_eq' (by rfl)) ((ComplexShape.up ℕ).next_eq' (by rfl))).hom ≫
      ((P.complex.linearYonedaObj R N).sc' n (n+1) (n+2)).moduleCatCyclesIso.hom ≫
        ModuleCat.ofHom (projectiveResolutionNativeHomCycleExtLinearMap P N (n+1)) := by
  have hq : ((P.complex.linearYonedaObj R N).sc' n (n+1) (n+2)).moduleCatLeftHomologyData.π ≫
      (projectiveResolutionNativeHomPositiveCohomologyQuotientEquiv P N n).toModuleIso.hom =
      ModuleCat.ofHom (projectiveResolutionNativeHomCycleExtLinearMap P N (n+1)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((projectiveResolutionNativeHomCycleExtLinearMap P N (n+1)).quotKerEquivOfSurjective
      (projectiveResolutionNativeHomCycleExtLinearMap_surjective P N (n+1)))
        ((Submodule.quotEquivOfEq _ _
          (projectiveResolutionNativeHomCycleExtLinearMap_kernel P N n).symm)
            (Submodule.Quotient.mk z)) = _
    rw [Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk]
    rfl
  simp only [projectiveResolutionNativeHomPositiveCohomologyIso,Iso.trans_hom,Category.assoc]
  rw [reassoc_of% (HomologicalComplex.π_homologyIsoSc'_hom
    (P.complex.linearYonedaObj R N) n (n+1) (n+2)
      ((ComplexShape.up ℕ).prev_eq' (by rfl)) ((ComplexShape.up ℕ).next_eq' (by rfl)))]
  rw [reassoc_of% (ShortComplex.π_moduleCatCyclesIso_hom
    ((P.complex.linearYonedaObj R N).sc' n (n+1) (n+2))),hq]

end LinearStudy
