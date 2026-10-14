module
public import Linear.KoszulNativeHomTopCohomology
public import Linear.TildePreservesMono
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- ACTUAL associated original Hom top homology data obtained by mapping
PROVED native data through PROVED exact associated-sheaf construction. -/
def tildeKoszulNativeHomTopHomologyData (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (((affineKoszulNativeHomCochainComplex R N (n+1) H).sc' n (n+1) (n+2)).map
      (tilde.functor R)).LeftHomologyData := by
  letI := tilde_functor_preservesHomology R
  exact (koszulNativeHomTopHomologyData R N n H).left.map (tilde.functor R)

/-- ACTUAL top cohomology of SAME original associated native-Hom complex
is SAME original associated N/IN;no source or coefficient conditions added. -/
def tildeKoszulNativeHomTopCohomologyIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (affineKoszulNativeHomCochainComplex R N (n+1) H)).homology (n+1) ≅
        tilde (ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)))) :=
  (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (affineKoszulNativeHomCochainComplex R N (n+1) H)).homologyIsoSc' n (n+1) (n+2)
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl)) ≪≫
      (tildeKoszulNativeHomTopHomologyData R N n H).homologyIso

/-- SAME actual class map retains EXACT original coefficient restriction
morphism after tilde. This is an actual sheaf morphism square. -/
theorem tildeKoszulNativeHomTopCohomologyIso_restriction (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (affineKoszulNativeHomCochainComplex R N (n+1) H)).homologyπ (n+1) ≫
      (tildeKoszulNativeHomTopCohomologyIso R N n H).hom =
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (affineKoszulNativeHomCochainComplex R N (n+1) H)).iCycles (n+1) ≫
      (tilde.functor R).map (koszulNativeHomTopRestrictionMorphism R N n H) := by
  have hc := (tildeKoszulNativeHomTopHomologyData R N n H).cyclesIso_hom_comp_i
  change (tildeKoszulNativeHomTopHomologyData R N n H).cyclesIso.hom ≫
    (tilde.functor R).map (𝟙 _) = _ at hc
  erw [CategoryTheory.Functor.map_id,Category.comp_id] at hc
  simp only [tildeKoszulNativeHomTopCohomologyIso,Iso.trans_hom,← Category.assoc]
  rw [HomologicalComplex.π_homologyIsoSc'_hom,Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  change _ ≫ ((tildeKoszulNativeHomTopHomologyData R N n H).cyclesIso.hom ≫
    (tilde.functor R).map (koszulNativeHomTopRestrictionMorphism R N n H)) = _
  rw [hc,← Category.assoc]
  erw [HomologicalComplex.cyclesIsoSc'_hom_iCycles]

end LinearStudy
